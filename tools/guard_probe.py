#!/usr/bin/env python3
from __future__ import annotations
import json
import datetime
import pathlib
from apps.hyperrag.guard import evaluate_action

ACTIONS = [
    ("graph.upsert_entity", {"etype": "Concept"}),
    ("graph.upsert_hyperedge", {"relation": "mentions", "arity": 2}),
    ("graph.relate", {"relation": "mentions"}),
    ("hyperrag.extract", {"approx_len": 123}),
]


def main() -> int:
    stamp = datetime.datetime.utcnow().strftime("%Y%m%d-%H%M%S")
    outdir = pathlib.Path("docs/audit/guard_probe") / stamp
    outdir.mkdir(parents=True, exist_ok=True)
    rows = []
    for action, ctx in ACTIONS:
        rows.append(
            {"action": action, "decision": evaluate_action(action, ctx), "context": ctx}
        )
    (outdir / "report.json").write_text(
        json.dumps(
            {
                "timestamp_utc": datetime.datetime.utcnow().isoformat(
                    timespec="seconds"
                )
                + "Z",
                "results": rows,
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    print(f"guard probe → {outdir}/report.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
