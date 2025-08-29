#!/usr/bin/env python3
"""
Canonical accuracy receipt emitter.

Writes receipts/_last/{scierc|biored}_scores_ml_test.json with schema:
{
  "micro": { "P": float, "R": float, "F1": float, "tp": int, "fp": int, "fn": int },
  "meta":  { "dataset": "SciERC|BioRED", "split": "test", "generated_at": ISO8601, "version": "semver" }
}
"""
from __future__ import annotations

import argparse
import json
import os
import time
from typing import Dict

ALLOWED = {"SciERC": "scierc", "BioRED": "biored"}


def write_receipt(
    dataset: str,
    micro: Dict[str, float],
    dest: str = "receipts/_last",
    split: str = "test",
    version: str = "0.1.0",
) -> str:
    ds_key = ALLOWED.get(dataset)
    if not ds_key:
        raise SystemExit(
            f"Unsupported dataset '{dataset}'. Allowed: {', '.join(ALLOWED)}"
        )
    os.makedirs(dest, exist_ok=True)
    payload = {
        "micro": {
            "P": float(micro["P"]),
            "R": float(micro["R"]),
            "F1": float(micro["F1"]),
            "tp": int(micro["tp"]),
            "fp": int(micro["fp"]),
            "fn": int(micro["fn"]),
        },
        "meta": {
            "dataset": dataset,
            "split": split,
            "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "version": version,
        },
    }
    out = os.path.join(dest, f"{ds_key}_scores_ml_{split}.json")
    with open(out, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)
    return out


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--dataset", required=True, choices=list(ALLOWED))
    p.add_argument("--P", type=float, required=True)
    p.add_argument("--R", type=float, required=True)
    p.add_argument("--F1", type=float, required=True)
    p.add_argument("--tp", type=int, required=True)
    p.add_argument("--fp", type=int, required=True)
    p.add_argument("--fn", type=int, required=True)
    p.add_argument("--dest", default="receipts/_last")
    p.add_argument("--split", default="test")
    p.add_argument("--version", default="0.1.0")
    args = p.parse_args()

    out = write_receipt(
        dataset=args.dataset,
        micro={
            "P": args.P,
            "R": args.R,
            "F1": args.F1,
            "tp": args.tp,
            "fp": args.fp,
            "fn": args.fn,
        },
        dest=args.dest,
        split=args.split,
        version=args.version,
    )
    print(f"✓ Wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
