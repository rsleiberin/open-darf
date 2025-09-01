#!/usr/bin/env python3
import argparse
import json
import os
import time
import collections
import torch
from transformers import AutoTokenizer, AutoModelForTokenClassification, pipeline


def read_jsonl(path, limit=None):
    with open(path, encoding="utf-8") as f:
        for i, line in enumerate(f):
            if limit is not None and i >= limit:
                break
            if line.strip():
                yield json.loads(line)


def extract_text(ex):
    text = ex.get("text")
    if text:
        return text
    parts = []
    for p in ex.get("passages") or []:
        t = p.get("text")
        if isinstance(t, list):
            parts.extend(t)
        elif isinstance(t, str):
            parts.append(t)
    return "\n".join(parts).strip()


def norm(s):
    if s is None:
        return None
    if isinstance(s, list):
        s = " ".join(map(str, s))
    s = str(s).strip().lower()
    return " ".join(s.split())


def gold_strings(ex):
    S = set()
    for e in ex.get("entities") or []:
        s = norm(e.get("text"))
        if s:
            S.add(s)
    for p in ex.get("passages") or []:
        for e in p.get("entities") or []:
            s = norm(e.get("text"))
            if s:
                S.add(s)
    return S


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--split", choices=["dev", "test"], required=True)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--model", default="d4data/biomedical-ner-all")
    ap.add_argument("--data_root", default="data/biored_official")
    args = ap.parse_args()

    os.makedirs(args.outdir, exist_ok=True)
    src = os.path.join(args.data_root, f"{args.split}.jsonl")
    docs = []
    for ex in read_jsonl(src, limit=args.limit):
        gid = str(ex.get("id") or ex.get("pmid") or "")
        txt = extract_text(ex)
        if gid and txt:
            docs.append({"id": gid, "text": txt})

    device = 0 if torch.cuda.is_available() else -1
    tok = AutoTokenizer.from_pretrained(args.model)
    mdl = AutoModelForTokenClassification.from_pretrained(args.model)
    ner = pipeline(
        "token-classification",
        model=mdl,
        tokenizer=tok,
        aggregation_strategy="simple",
        device=device,
    )

    pred_path = os.path.join(args.outdir, f"preds_{args.split}.jsonl")
    t0 = time.time()
    ent_total = 0
    label_counts = collections.Counter()
    with open(pred_path, "w", encoding="utf-8") as out:
        for d in docs:
            preds = ner(d["text"])
            sp = []
            for p in preds:
                q = dict(p)
                # cast to JSON-native
                if "score" in q:
                    q["score"] = float(q["score"])
                if "start" in q:
                    q["start"] = int(q["start"])
                if "end" in q:
                    q["end"] = int(q["end"])
                sp.append(q)
                lab = q.get("entity_group")
                if lab:
                    label_counts[str(lab)] += 1
            ent_total += len(sp)
            out.write(
                json.dumps({"id": d["id"], "preds": sp}, ensure_ascii=False) + "\n"
            )
    t1 = time.time()

    # Evaluate (string-match)
    gold_by_id = {}
    for ex in read_jsonl(src, limit=args.limit):
        gid = str(ex.get("id") or ex.get("pmid") or "")
        if gid:
            gold_by_id[gid] = gold_strings(ex)

    tp = fp = fn = 0
    docs_scored = 0
    with open(pred_path, encoding="utf-8") as f:
        for line in f:
            rec = json.loads(line)
            gid = rec.get("id")
            if not gid or gid not in gold_by_id:
                continue
            preds = set(
                norm(p.get("word")) for p in rec.get("preds", []) if norm(p.get("word"))
            )
            gold = gold_by_id[gid]
            tp += len(preds & gold)
            fp += len(preds - gold)
            fn += len(gold - preds)
            docs_scored += 1
    P = tp / (tp + fp) if (tp + fp) > 0 else 0.0
    R = tp / (tp + fn) if (tp + fn) > 0 else 0.0
    F1 = (2 * P * R / (P + R)) if (P + R) > 0 else 0.0

    summary = {
        "status": "ok",
        "split": args.split,
        "model": args.model,
        "device": "cuda" if device == 0 else "cpu",
        "docs": len(docs),
        "pred_entities": ent_total,
        "labels": dict(label_counts),
        "precision": P,
        "recall": R,
        "entity_f1": F1,
        "wall_seconds": round(t1 - t0, 4),
    }
    open(os.path.join(args.outdir, f"summary_{args.split}.json"), "w").write(
        json.dumps(summary, indent=2)
    )
    open(os.path.join(args.outdir, f"metrics_{args.split}.json"), "w").write(
        json.dumps(
            {
                "task": "biored_ner_stringmatch",
                "split": args.split,
                "micro": {"tp": tp, "fp": fp, "fn": fn, "P": P, "R": R, "F1": F1},
                "docs_scored": docs_scored,
            },
            indent=2,
        )
    )
    print(json.dumps({"wrote": [pred_path], **summary}, indent=2))


if __name__ == "__main__":
    main()
