#!/usr/bin/env python3
from __future__ import annotations
import sys
import os
import json
import datetime
from apps.hyperrag.extract import RegexEntityExtractor
from apps.hyperrag.model import new_id, Fact, HyperEdge


def main() -> int:
    text = sys.stdin.read().strip()
    if not text:
        print("No input text on stdin", file=sys.stderr)
        return 2
    extr = RegexEntityExtractor()
    ents = extr.extract(text)
    # trivial relation: "mentions" linking all entities in one hyperedge
    edge = HyperEdge(
        uid=new_id("hedge"),
        relation="mentions",
        participants=[("arg", e.uid) for e in ents],
    )
    fact = Fact(uid=new_id("fact"), edge=edge, confidence=0.1)
    stamp = datetime.datetime.utcnow().strftime("%Y%m%d-%H%M%S")
    outdir = os.path.join("docs", "audit", "hyperrag", stamp)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "receipt.json"), "w", encoding="utf-8") as f:
        f.write(
            json.dumps(
                {
                    "timestamp_utc": datetime.datetime.utcnow().isoformat(
                        timespec="seconds"
                    )
                    + "Z",
                    "entities": [
                        vars(e) | {"span": vars(e.span) if e.span else None}
                        for e in ents
                    ],
                    "fact": json.loads(fact.to_json()),
                },
                ensure_ascii=False,
            )
        )
    print(f"receipt → {outdir}/receipt.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
