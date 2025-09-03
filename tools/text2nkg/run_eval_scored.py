import os, json, time, argparse, subprocess, hashlib
from typing import Dict, Any, List, Tuple, Optional
from tools.text2nkg.adapter import get_adapter
from tools.text2nkg.emit_nkg import emit_nkg
from tools.constitutional import hooks
from tools.text2nkg.gold_utils import discover_gold

def file_sha256(path: str) -> str:
    try:
        h=hashlib.sha256()
        with open(path,'rb') as f:
            for chunk in iter(lambda:f.read(1<<20), b''):
                h.update(chunk)
        return h.hexdigest()
    except Exception as e:
        return f"error:{e}"

def git_meta():
    def g(args):
        try:
            return subprocess.check_output(["git"]+args, text=True).strip()
        except Exception:
            return "n/a"
    return {
        "branch": g(["rev-parse","--abbrev-ref","HEAD"]),
        "head": g(["rev-parse","--short=12","HEAD"]),
        "dirty": g(["status","--porcelain"]) != "",
    }

def load_sentences(path: str) -> List[Dict[str,Any]]:
    sents=[]
    with open(path,"r",encoding="utf-8") as f:
        for i, line in enumerate(f):
            o=json.loads(line)
            text = o.get("text") or o.get("sentence") or o.get("raw","")
            sents.append({"sid": o.get("id", i), "text": text})
    return sents

def score_sets(pred: List[Tuple[int,int,str]], gold: List[Tuple[int,int,str]], labeled: bool):
    P = {(a,b,(l if labeled else None)) for a,b,l in pred}
    G = {(a,b,(l if labeled else None)) for a,b,l in gold}
    tp = len(P & G)
    return tp, len(P), len(G)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", choices=["biored","scierc"], required=True)
    ap.add_argument("--split", choices=["dev","test"], default="dev")
    ap.add_argument("--config", default="var/config/text2nkg_config.json")
    ap.add_argument("--outdir", default=None)
    args = ap.parse_args()

    cfg = {}
    if os.path.exists(args.config):
        with open(args.config,"r") as f:
            cfg=json.load(f)

    # Local-only model mapping (won't fetch)
    model_map = cfg.get("ner_model_path_map", {
        "scierc": os.path.expanduser("~/.darf/models/scibert-scivocab-uncased"),
        "biored": os.path.expanduser("~/.darf/models/biobert-base-cased-v1.1")
    })
    cfg["ner_model_path"] = model_map.get(args.dataset, cfg.get("ner_model_path", model_map.get("scierc")))
    cfg["local_files_only"] = True

    # Sentence source
    if args.dataset=="biored":
        sent_path=f"var/datasets/text/biored_by_sentence/{args.split}.jsonl"
    else:
        sent_path=f"var/datasets/text/scierc_by_sentence/{args.split}.jsonl"
    os.makedirs(os.path.dirname(sent_path), exist_ok=True)
    if not os.path.exists(sent_path):
        with open(sent_path,"w",encoding="utf-8") as w:
            w.write(json.dumps({"id": 0, "text": ""})+"\n")

    sents=load_sentences(sent_path)

    adapter=get_adapter(cfg)
    preds=list(adapter.predict(sents))  # each p is expected to expose .spans (start,end,label)

    stamp=time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir=args.outdir or f"var/receipts/phase7a/text2nkg/{args.dataset}_{args.split}_{stamp}"
    os.makedirs(outdir, exist_ok=True)

    # Emit NKG (graph)
    run_meta={"dataset": args.dataset, "split": args.split, "cfg": cfg, "git": git_meta(),
              "env": {"TRANSFORMERS_OFFLINE": os.getenv("TRANSFORMERS_OFFLINE")},
              "sentence_path": sent_path, "sentence_sha256": file_sha256(sent_path)}
    nkg=emit_nkg(sents, preds, run_meta)
    with open(os.path.join(outdir,"nkg.json"),"w") as f: json.dump(nkg, f, indent=2)

    # Dump raw predicted spans (for inspection)
    with open(os.path.join(outdir,"pred_spans.jsonl"),"w",encoding="utf-8") as w:
        for s, p in zip(sents, preds):
            spans = [{"start": int(sp.get("start")), "end": int(sp.get("end")), "label": str(sp.get("label",""))}
                     for sp in getattr(p,"spans",[]) if isinstance(sp.get("start"),int) and isinstance(sp.get("end"),int)]
            w.write(json.dumps({"id": s["sid"], "text_len": len(s["text"]), "spans": spans}, ensure_ascii=False)+"\n")

    # Audit (latency only)
    from tools.constitutional import hooks
    lat=[]
    with open(os.path.join(outdir,"audit.jsonl"),"w",encoding="utf-8") as stream:
        for s, p in zip(sents, preds):
            spans_n=len(getattr(p,"spans",[])); rels_n=len(getattr(p,"relations",[]))
            state, pr, conf, us = hooks.decide(
                action="emit_sentence_graph",
                context={"dataset": args.dataset, "split": args.split, "sid": s["sid"],
                         "text_len": len(s["text"]), "spans": spans_n, "relations": rels_n}
            )
            stream.write(json.dumps({"ts": time.time(), "dataset": args.dataset, "split": args.split,
                                     "sid": s["sid"], "state": state, "principles": pr,
                                     "confidence": conf, "elapsed_us": us})+"\n")
            lat.append(us)
    with open(os.path.join(outdir,"audit_summary.json"),"w") as f:
        f.write(json.dumps({
            "calls": len(lat),
            "elapsed_us_avg": (sum(lat)/len(lat)) if lat else 0.0
        }, indent=2))

    # --- GOLD DISCOVERY + SCORING ---
    gold_path, gold = discover_gold(args.dataset, args.split)
    # gold: Dict[sid, List[Tuple[int,int,str]]]
    # Build per-sid gold sets once
    gold_total = sum(len(v) for v in gold.values())

    pred_total=0
    tp_strict=0
    tp_unlab=0

    with open(os.path.join(outdir,"pred_spans.jsonl"), "r", encoding="utf-8") as fin:
        for i, line in enumerate(fin):
            o=json.loads(line)
            sid=o.get("id", i)
            pred = [(int(s["start"]), int(s["end"]), str(s.get("label",""))) for s in o.get("spans",[])]
            g = gold.get(sid, [])
            # strict (label-aware)
            a, pN, gN = score_sets(pred, g, labeled=True)
            tp_strict += a
            pred_total += pN
            # unlabeled
            a2, _, _ = score_sets(pred, g, labeled=False)
            tp_unlab += a2

    def prf(tp, pN, gN):
        prec = (tp/pN) if pN else 0.0
        rec  = (tp/gN) if gN else 0.0
        f1   = (2*prec*rec/(prec+rec)) if (prec+rec) else 0.0
        return prec, rec, f1

    p_strict, r_strict, f1_strict = prf(tp_strict, pred_total, gold_total)
    p_unlab,  r_unlab,  f1_unlab  = prf(tp_unlab,  pred_total, gold_total)

    metrics = {
        "adapter": adapter.__class__.__name__,
        "pred_span_count": pred_total,
        "gold_source": gold_path,
        "entities_strict_span": {
            "tp": tp_strict, "pred_total": pred_total, "gold_total": gold_total,
            "precision": p_strict, "recall": r_strict, "f1": f1_strict
        },
        "entities_unlabeled_span": {
            "tp": tp_unlab, "pred_total": pred_total, "gold_total": gold_total,
            "precision": p_unlab, "recall": r_unlab, "f1": f1_unlab
        }
    }
    with open(os.path.join(outdir,"metrics.json"),"w") as f:
        json.dump(metrics, f, indent=2)

    print(f"✓ NKG written: {outdir}/nkg.json")
    print(f"✓ Pred spans: {outdir}/pred_spans.jsonl")
    print(f"✓ Metrics   : {outdir}/metrics.json")
    print(f"Adapter: {adapter.__class__.__name__}")
    print(f"Gold: {gold_path}  (gold_total={gold_total})")
if __name__ == "__main__":
    main()
