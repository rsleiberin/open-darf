#!/usr/bin/env python3
"""Emit deterministic relation metrics receipts (no network, stdlib-only).

Input JSONL lines:
{
  "doc_id": "D1",
  "entities": [{"id": "T1","type":"Gene","sent":0}, ...],
  "relations": [{"head":"T1","tail":"T2","type":"affects"}, ...]  # gold
}

We deliberately produce **no** predicted relations in Phase-6C (hermetic placeholder),
so micro-F1 will be 0 unless gold is empty. This mirrors the current recorded 0.0.
"""
from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from typing import Dict, List, Set, Tuple

try:
    from .score_relations import predict_heuristic
except Exception:
    # allow running as a flat script
    from scripts.relation_extraction.score_relations import predict_heuristic  # type: ignore


def _read_jsonl(path: str) -> List[Dict]:
    with open(path, "r", encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def _micro_prf1(
    gold: Set[Tuple[str, str, str]], pred: Set[Tuple[str, str, str]]
) -> Dict[str, float]:
    tp = len(gold & pred)
    fp = len(pred - gold)
    fn = len(gold - pred)
    p = tp / (tp + fp) if (tp + fp) else 0.0
    r = tp / (tp + fn) if (tp + fn) else 0.0
    f1 = (2 * p * r / (p + r)) if (p + r) else 0.0
    return {"precision": p, "recall": r, "f1": f1, "support": float(len(gold))}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--input", required=True, help="Toy JSONL with entities and gold relations"
    )
    ap.add_argument(
        "--out", default="var/receipts/phase6c/validation/biored_relations_scores.json"
    )
    args = ap.parse_args()

    rows = _read_jsonl(args.input)
    gold: Set[Tuple[str, str, str]] = set()
    # Placeholder: predicted set is empty to remain hermetic and match current baseline.
    pred: Set[Tuple[str, str, str]] = set()

    for row in rows:
        for rel in row.get("relations", []):
            h, t = rel["head"], rel["tail"]
            head, tail = (h, t) if h <= t else (t, h)
            gold.add((head, tail, rel.get("type", "UNK")))

    # Optional prediction path (heuristic, deterministic)
    if args.predictor == "heuristic":
        # Build (ordered) candidates from entities in the same sentence
        ent_types = {
            e["id"]: e.get("type", "UNK")
            for row in rows
            for e in row.get("entities", [])
        }
        # naive sentence-bucketed candidate gen
        buckets = {}
        for row in rows:
            for e in row.get("entities", []):
                buckets.setdefault(int(e.get("sent", 0)), []).append(e["id"])
        cands = []
        for ids in buckets.values():
            ids = sorted(ids)
            for i in range(len(ids)):
                for j in range(i + 1, len(ids)):
                    cands.append((ids[i], ids[j]))
        pred = predict_heuristic(cands, ent_types)

        m = _micro_prf1(gold, pred)
    out = {
        "version": "phase6c",
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "biored": {
            "relation_precision": m["precision"],
            "relation_recall": m["recall"],
            "relation_f1": m["f1"],
            "support": int(m["support"]),
        },
        "by_type": {},
    }
    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False, indent=2)
        fh.write("\n")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
