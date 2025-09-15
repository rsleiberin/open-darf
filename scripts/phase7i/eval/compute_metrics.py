#!/usr/bin/env python3
"""
Compute micro-precision/recall/F1 over labeled (head,tail,relation) and
unlabeled F1 over (head,tail), given predictions and gold.

Usage:
  compute_metrics.py --preds PRED.jsonl --gold GOLD.jsonl --out METRICS.json
         [--gpu-mb N] [--comp-rate X] [--dataset DS] [--split SPLIT] [--model M]
"""
import argparse, json
from adapters import load_any

def f1_prec_rec(gold_set, pred_set):
    tp = len(gold_set & pred_set)
    fp = len(pred_set - gold_set)
    fn = len(gold_set - pred_set)
    p = tp / (tp + fp) if (tp + fp) > 0 else 0.0
    r = tp / (tp + fn) if (tp + fn) > 0 else 0.0
    f1 = 2*p*r/(p+r) if (p+r)>0 else 0.0
    return f1, p, r

def as_pairs(rows, labeled=True):
    if labeled:
        return set((r.get("head",""), r.get("tail",""), r.get("relation","")) for r in rows if r.get("head") and r.get("tail"))
    return set((r.get("head",""), r.get("tail","")) for r in rows if r.get("head") and r.get("tail"))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--preds", required=True)
    ap.add_argument("--gold", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--gpu-mb", type=float, default=0.0)
    ap.add_argument("--comp-rate", type=float, default=0.95)
    ap.add_argument("--dataset", default="")
    ap.add_argument("--split", default="test")
    ap.add_argument("--model", default="")
    args = ap.parse_args()

    preds = list(load_any(args.preds))
    gold  = list(load_any(args.gold))

    pred_l = as_pairs(preds, labeled=True)
    gold_l = as_pairs(gold, labeled=True)
    pred_u = as_pairs(preds, labeled=False)
    gold_u = as_pairs(gold, labeled=False)

    f1_l, p_l, r_l = f1_prec_rec(gold_l, pred_l)
    f1_u, _, _     = f1_prec_rec(gold_u, pred_u)

    out = {
        "dataset": args.dataset,
        "split": args.split,
        "model": args.model,
        "precision_micro": round(p_l, 6),
        "recall_micro": round(r_l, 6),
        "f1_micro": round(f1_l, 6),
        "f1_unlabeled": round(f1_u, 6),
        "pred_count": len(pred_l),
        "gold_pairs": len(gold_l),
        "latency_ms": 0.0,
        "gpu_mem_mb": args.gpu_mb,
        "constitutional_compliance_rate": max(0.0, min(1.0, args.comp_rate))
    }

    with open(args.out, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=2)

if __name__ == "__main__":
    main()
