#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
import json
import os
import time
import tempfile
from pathlib import Path
from statistics import mean
from apps.document_processor import bias

SAMPLE = "We present results but offer no methodology. Clearly this is the best outcome. [1] doi:10.1/abc"


def time_many(n: int, *, emit: bool, receipts_dir: str) -> float:
    os.environ["RECEIPTS_PATH"] = receipts_dir
    lat = []
    for _ in range(n):
        t0 = time.perf_counter()
        _ = bias.classify_text(SAMPLE, threshold=0.4, emit_receipt=emit)
        lat.append((time.perf_counter() - t0) * 1000.0)
    return mean(lat)


def main():
    n = int(os.getenv("CBDT_PERF_N", "50"))
    with tempfile.TemporaryDirectory() as d:
        t_no = time_many(n, emit=False, receipts_dir=d)
        t_yes = time_many(n, emit=True, receipts_dir=d)
    metrics = {
        "n": n,
        "avg_ms_no_receipts": t_no,
        "avg_ms_with_receipts": t_yes,
        "overhead_ms": t_yes - t_no,
        "overhead_pct": ((t_yes - t_no) / max(1e-9, t_no)) * 100.0,
        "limit_ms_per_doc": 2000.0,
    }
    outdir = Path("docs/audit/cbdt_perf")
    outdir.mkdir(parents=True, exist_ok=True)
    ts = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    path = outdir / f"metrics-{ts}.json"
    path.write_text(json.dumps(metrics, indent=2))
    print(json.dumps(metrics, indent=2))
    print(f"Wrote {path}")


if __name__ == "__main__":
    main()
