import os
import random
import time
import json
from pathlib import Path
import pytest
from apps.hyperrag.index_sim import IndexSim

RUN = os.getenv("RUN_PERF") == "1"
WRITE = os.getenv("WRITE_RECEIPTS") == "1"
CI = os.getenv("CI") == "true"

pytestmark = pytest.mark.skipif(not RUN, reason="perf suite gated by RUN_PERF=1")


def _synth(seed=7, n_heads=2000, n_roles=6, avg_deg=4):
    random.seed(seed)
    roles = [f"r{i}" for i in range(n_roles)]
    facts = []
    for h in range(n_heads):
        head = f"H{h}"
        # draw deg from 1..(2*avg_deg)
        deg = random.randint(1, 2 * avg_deg)
        for _ in range(deg):
            r = random.choice(roles)
            t = f"T{random.randint(0, n_heads*2)}"
            facts.append((head, r, t))
    return facts, roles


def test_role_fanout_perf(tmp_path: Path):
    facts, roles = _synth()
    idx = IndexSim(facts)
    heads = [f"H{i}" for i in range(2000)]
    times = []
    # Query cycle: role-scoped fanout & neighbors
    t_start = time.perf_counter()
    for i, h in enumerate(heads * 2):  # ~4000 ops
        role = roles[i % len(roles)]
        ts = time.perf_counter()
        _ = idx.fanout_count(h, role)
        _ = idx.neighbors(h, role)
        times.append((time.perf_counter() - ts) * 1000.0)
    total_ms = (time.perf_counter() - t_start) * 1000.0
    p95 = sorted(times)[int(0.95 * len(times)) - 1]
    avg = sum(times) / len(times)
    # Generous thresholds to keep CI stable and well < target 10ms p95
    assert p95 < 5.0
    assert avg < 2.0

    receipt = {
        "suite": "storage_fanout",
        "samples": len(times),
        "ms": {"p95": round(p95, 3), "avg": round(avg, 3), "total": round(total_ms, 3)},
    }
    # Always tmp; optional mirror when WRITE_RECEIPTS=1 and not CI
    (tmp_path / "storage_fanout.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8"
    )
    if WRITE and not CI:
        ts = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
        root = Path("docs/audit")
        (root / "_last").mkdir(parents=True, exist_ok=True)
        (root / "phase4" / ts).mkdir(parents=True, exist_ok=True)
        for p in (
            root / "_last" / "storage_fanout.json",
            root / "phase4" / ts / "storage_fanout.json",
        ):
            p.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
