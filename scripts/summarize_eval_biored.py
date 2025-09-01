#!/usr/bin/env python3
import argparse
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("--in", dest="in_dir", required=True)
ap.add_argument("--out", required=True)
args = ap.parse_args()
m = json.loads((Path(args.in_dir) / "metrics.json").read_text())
summary = {
    "task": "biored",
    "model": m["model"],
    "micro": {
        "entity_f1": m["micro_entity"]["f1"],
        "relation_f1": m["micro_relation"]["f1"],
    },
    "timing": m.get("timing", {}),
}
Path(args.out).write_text(json.dumps(summary, indent=2))
print(
    json.dumps(
        {
            "wrote": args.out,
            "entity_f1": summary["micro"]["entity_f1"],
            "relation_f1": summary["micro"]["relation_f1"],
        }
    )
)
