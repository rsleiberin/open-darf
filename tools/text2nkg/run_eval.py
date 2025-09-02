import os, json, time, argparse
from typing import Dict, Any, List
from tools.text2nkg.adapter import get_adapter
from tools.text2nkg.emit_nkg import emit_nkg
from tools.constitutional import hooks

import subprocess, hashlib

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
            obj=json.loads(line)
            text=obj.get("text") or obj.get("sentence") or obj.get("raw","")
            sents.append({"sid": obj.get("id", i), "text": text})
    return sents

def percentile(values, p):
    if not values: return 0.0
    k = max(0, min(len(values)-1, int(len(values)*p)))
    return sorted(values)[k]

def audit_sentence(stream, dataset: str, split: str, s: Dict[str,Any], spans_n: int, rels_n: int) -> float:
    state, principles, conf, elapsed_us = hooks.decide(
        action="emit_sentence_graph",
        context={"dataset": dataset, "split": split, "sid": s.get("sid"), "text_len": len(s.get("text","")), "spans": spans_n, "relations": rels_n}
    )
    stream.write(json.dumps({
        "ts": time.time(), "dataset": dataset, "split": split, "sid": s.get("sid"),
        "state": state, "principles": principles, "confidence": conf, "elapsed_us": elapsed_us
    }) + "\n")
    return elapsed_us

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", choices=["biored","scierc"], required=True)
    ap.add_argument("--split", choices=["dev","test"], default="dev")
    ap.add_argument("--config", default="var/config/text2nkg_config.json")
    ap.add_argument("--outdir", default=None)
    args = ap.parse_args()

    with open(args.config,"r") as f:
        cfg=json.load(f)

    # Dataset→model path mapping (local-only). Falls back gracefully if missing.
    model_map = cfg.get("ner_model_path_map", {
        "scierc": os.path.expanduser("~/.darf/models/scibert-scivocab-uncased"),
        "biored": os.path.expanduser("~/.darf/models/biobert-base-cased-v1.1")
    })
    cfg["ner_model_path"] = model_map.get(args.dataset, cfg.get("ner_model_path", model_map.get("scierc")))
    cfg["local_files_only"] = True  # force hermetic

    # Sentence sources
    if args.dataset=="biored":
        sent_path=f"var/datasets/text/biored_by_sentence/{args.split}.jsonl"
    else:
        sent_path=f"var/datasets/text/scierc_by_sentence/{args.split}.jsonl"

    if not os.path.exists(sent_path):
        os.makedirs(os.path.dirname(sent_path), exist_ok=True)
        with open(sent_path,"w",encoding="utf-8") as w:
            w.write(json.dumps({"id": 0, "text": "Placeholder sentence for hermetic dry-run."})+"\n")

    sents=load_sentences(sent_path)
    adapter=get_adapter(cfg)
    preds=list(adapter.predict(sents))
    stamp=time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir=args.outdir or f"var/receipts/phase7a/text2nkg/{args.dataset}_{args.split}_{stamp}"
    os.makedirs(outdir, exist_ok=True)

    # Emit NKG
    run_meta={"dataset": args.dataset, "split": args.split, "cfg": cfg, "git": git_meta(), "env": {"TRANSFORMERS_OFFLINE": os.getenv("TRANSFORMERS_OFFLINE"), "HF_HUB_DISABLE_TELEMETRY": os.getenv("HF_HUB_DISABLE_TELEMETRY")}, "sentence_path": sent_path, "sentence_sha256": file_sha256(sent_path)}
    nkg=emit_nkg(sents, preds, run_meta)
    with open(os.path.join(outdir,"nkg.json"),"w") as f: json.dump(nkg, f, indent=2)

    # Metrics
    spans_total = sum(len(getattr(p,"spans",[])) for p in preds)
    rels_total  = sum(len(getattr(p,"relations",[])) for p in preds)
    metrics={"spans": spans_total, "relations": rels_total, "adapter": adapter.__class__.__name__}
    with open(os.path.join(outdir,"metrics.json"),"w") as f: json.dump(metrics, f, indent=2)

    # Constitutional audit
    lat_us=[]
    with open(os.path.join(outdir,"audit.jsonl"),"w",encoding="utf-8") as stream:
        for s, p in zip(sents, preds):
            spans_n = len(getattr(p,"spans",[])); rels_n = len(getattr(p,"relations",[]))
            lat_us.append(audit_sentence(stream, args.dataset, args.split, s, spans_n, rels_n))

    aud_sum = {
        "calls": len(lat_us),
        "elapsed_us_avg": (sum(lat_us)/len(lat_us)) if lat_us else 0.0,
        "p50_us": percentile(lat_us, 0.50),
        "p95_us": percentile(lat_us, 0.95),
        "p99_us": percentile(lat_us, 0.99)
    }
    with open(os.path.join(outdir,"audit_summary.json"),"w") as f: json.dump(aud_sum, f, indent=2)

    print(f"✓ NKG written: {outdir}/nkg.json")
    print(f"✓ Metrics written: {outdir}/metrics.json")
    print(f"✓ Audit written: {outdir}/audit.jsonl")
    print(f"✓ Audit summary: {outdir}/audit_summary.json")
    print(f"Adapter: {adapter.__class__.__name__}")

if __name__=="__main__":
    main()
