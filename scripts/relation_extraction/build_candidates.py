#!/usr/bin/env python3
"""Build relation candidates from a tiny, deterministic JSONL schema.

Input JSONL lines:
{
  "doc_id": "D1",
  "entities": [{"id": "T1", "type": "Gene", "sent": 0}, ...]
}
Outputs JSONL with {"doc_id": "...", "candidates": [["T1","T2"], ...]}
"""
from __future__ import annotations

import argparse
import json
import sys
from typing import List, Dict

from .common import Entity, generate_candidates


def _read_jsonl(path: str) -> List[Dict]:
    with sys.stdin if path == "-" else open(path, "r", encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True, help="Path to JSONL (or '-' for stdin)")
    ap.add_argument("--out", required=True, help="Output JSONL file for candidates")
    args = ap.parse_args()

    rows = _read_jsonl(args.input)
    with open(args.out, "w", encoding="utf-8") as out:
        for row in rows:
            ents = [
                Entity(e["id"], e.get("type", "UNK"), int(e.get("sent", 0)))
                for e in row.get("entities", [])
            ]
            cands = generate_candidates(ents)
            json.dump({"doc_id": row.get("doc_id", ""), "candidates": cands}, out)
            out.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
