#!/usr/bin/env python3
import glob
import json
import os
import sys
import time
from pathlib import Path


def load_jsonl(path):
    out = []
    try:
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    out.append(json.loads(line))
                except Exception:
                    pass
    except FileNotFoundError:
        pass
    return out


def main():
    dest = (
        Path(sys.argv[1])
        if len(sys.argv) > 1
        else Path("docs/audit/phase6b_ml_execution/_ad-hoc/metrics")
    )
    dest.mkdir(parents=True, exist_ok=True)

    metrics_dir = Path(os.getenv("OBS_METRICS_DIR", "var/metrics"))
    # Accept both prefix and suffix snapshot patterns
    paths = glob.glob(str(metrics_dir / "*_snapshot.jsonl")) + glob.glob(
        str(metrics_dir / "snapshot_*.jsonl")
    )

    summary = {"generated_at": time.time(), "snapshot": {}}
    if not paths:
        summary["snapshot"] = {"note": "no snapshots found"}
    else:
        lines = []
        for p in paths:
            lines.extend(load_jsonl(p))
        # Keep only the last snapshot if many
        if lines:
            last = lines[-1]
            summary["snapshot"] = {
                "session": last.get("session"),
                "counters_keys": sorted(list((last.get("counters") or {}).keys())),
                "timers_keys": sorted(list((last.get("timers") or {}).keys())),
                "source": last.get("source", "n/a"),
            }
        else:
            summary["snapshot"] = {"note": "empty snapshot file(s)"}

    out_path = dest / "observability_summary.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
