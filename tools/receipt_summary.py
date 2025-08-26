#!/usr/bin/env python3
from __future__ import annotations
import json
import glob
import datetime
import pathlib

CATS = {
    "hyperrag_perf": (
        "docs/audit/hyperrag_perf/*/bench.json",
        ["p50_ms", "p95_ms", "p99_ms", "max_ms"],
    ),
    "qdrant_perf": (
        "docs/audit/qdrant_perf/*/bench.json",
        ["p50_ms", "p95_ms", "p99_ms", "max_ms"],
    ),
    "guard_perf": (
        "docs/audit/guard_perf/*/bench.json",
        ["p50_ms", "p95_ms", "max_ms"],
    ),
    "perf_sanity": ("docs/audit/perf_sanity/*/summary.json", ["extractor", "guard"]),
}


def latest(path_glob: str):
    paths = sorted(glob.glob(path_glob))
    return paths[-1] if paths else None


def pick_metrics(obj, keys):
    out = {}
    for k in keys:
        out[k] = obj.get(k)
    return out


def main() -> int:
    now = datetime.datetime.utcnow().strftime("%Y%m%d-%H%M%S")
    outdir = pathlib.Path("docs/audit/summary") / now
    outdir.mkdir(parents=True, exist_ok=True)
    summary = {
        "timestamp_utc": datetime.datetime.utcnow().isoformat(timespec="seconds") + "Z",
        "sources": {},
    }
    for cat, (pattern, keys) in CATS.items():
        p = latest(pattern)
        if not p:
            continue
        try:
            with open(p, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            continue
        summary["sources"][cat] = {"file": p, "metrics": pick_metrics(data, keys)}
    with open(outdir / "summary.json", "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)
    print(f"receipt summary → {outdir}/summary.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
