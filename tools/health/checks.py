from __future__ import annotations
import json
import pathlib
import sys

TARGETS = {
    "hybrid_e2e_p95_ms": 2000.0,
    "validation_overhead_p95_ms": 170.0,
}


def latest_perf_dir(root="var/receipts/perf"):
    rootp = pathlib.Path(root)
    if not rootp.exists():
        return None
    dirs = sorted(
        [p for p in rootp.iterdir() if p.is_dir()], key=lambda p: p.name, reverse=True
    )
    return dirs[0] if dirs else None


def load_report(pdir: pathlib.Path):
    f = pdir / "perf_report.json"
    if not f.exists():
        return None
    return json.loads(f.read_text(encoding="utf-8"))


def check(report: dict) -> int:
    bad = 0
    e2e = report.get("results", {}).get("hybrid_e2e", {}).get("latencies_ms", {})
    p95 = float(e2e.get("p95", 0.0))
    print(
        f"[hybrid_e2e] p95={p95:.2f} ms (target <= {TARGETS['hybrid_e2e_p95_ms']:.0f})"
    )
    if p95 > TARGETS["hybrid_e2e_p95_ms"]:
        bad += 1

    val = (
        report.get("results", {}).get("validation_overhead", {}).get("latencies_ms", {})
    )
    v95 = float(val.get("p95", 0.0))
    print(
        f"[validation_overhead] p95={v95:.2f} ms (target <= {TARGETS['validation_overhead_p95_ms']:.0f})"
    )
    if v95 > TARGETS["validation_overhead_p95_ms"]:
        bad += 1

    return bad


def main():
    pdir = latest_perf_dir()
    if not pdir:
        print("No perf receipts found (run RUN_PERF=1 tools/perf/run_perf.py)")
        sys.exit(0)
    report = load_report(pdir)
    if not report:
        print(f"No perf_report.json in {pdir}")
        sys.exit(1)
    failures = check(report)
    if failures:
        print(f"Health: FAIL ({failures} checks)")
        sys.exit(2)
    print("Health: OK")
    sys.exit(0)


if __name__ == "__main__":
    main()
