import json
import os
import statistics
import time
from pathlib import Path
import pytest
from apps.constitution_scope.scope import evaluate, Decision

RUN = os.getenv("RUN_PERF") == "1"
WRITE = os.getenv("WRITE_RECEIPTS") == "1"
CI = os.getenv("CI") == "true"
pytestmark = pytest.mark.skipif(not RUN, reason="perf suite gated by RUN_PERF=1")


def _role_rule(ctx):
    return {"decision": "ALLOW" if ctx.get("role") == "editor" else "DENY"}


def _bench_once(n: int = 5000):
    times = []
    start = time.perf_counter()
    for i in range(n):
        t0 = time.perf_counter()
        ctx = {"role": "editor"} if (i % 2 == 0) else {"role": "viewer"}
        out = evaluate(_role_rule, ctx)
        assert out["decision"] in (Decision.ALLOW, Decision.DENY)
        times.append((time.perf_counter() - t0) * 1000.0)
    total_ms = (time.perf_counter() - start) * 1000.0
    return times, total_ms


def test_scope_evaluate_perf_and_receipts(tmp_path: Path):
    times, total_ms = _bench_once(n=5000)
    p50 = statistics.median(times)
    p95 = sorted(times)[int(0.95 * len(times)) - 1]
    avg = sum(times) / len(times)
    mx = max(times)

    # Lenient thresholds (well within SLOs)
    assert p95 < 5.0
    assert avg < 2.0

    receipt = {
        "suite": "scope_evaluate",
        "samples": len(times),
        "ms": {
            "p50": round(p50, 3),
            "p95": round(p95, 3),
            "avg": round(avg, 3),
            "max": round(mx, 3),
            "total": round(total_ms, 3),
        },
        "target_ms": {"p95": 170.0},
    }

    # Always write to tmp_path (non-repo)
    (tmp_path / "scope_eval_perf.json").write_text(
        json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )

    # Only mirror into docs/ when explicitly requested AND not in CI
    if WRITE and not CI:
        ts = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
        root = Path("docs/audit")
        tsdir = root / "phase4" / ts
        tsdir.mkdir(parents=True, exist_ok=True)
        (root / "_last").mkdir(parents=True, exist_ok=True)
        for path in (
            tsdir / "scope_eval_perf.json",
            root / "_last" / "scope_eval_perf.json",
        ):
            path.write_text(
                json.dumps(receipt, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
            )
