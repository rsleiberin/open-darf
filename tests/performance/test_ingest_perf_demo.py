import os, json, glob, pytest
from pathlib import Path

TARGET_P95_MS = float(os.getenv("PHASE7C_P95_TARGET_MS", "170"))

def find_demo_dir():
    dd = os.getenv("PHASE7C_DEMO_DIR")
    if dd and Path(dd).exists():
        return Path(dd)
    cands = sorted(Path("var/receipts/phase7c").glob("demo_*"), reverse=True)
    return cands[0] if cands else None

def load_report(d: Path):
    for name in ("report_blocking_full.json", "report_blocking.json"):
        p = d / name
        if p.exists():
            return json.loads(p.read_text(encoding="utf-8"))
    return None

@pytest.mark.skipif(not Path("var/receipts/phase7c").exists(), reason="no Phase 7C demo present")
def test_ingest_timing_under_budget():
    d = find_demo_dir()
    if d is None:
        pytest.skip("no demo dir found")
    rep = load_report(d)
    if rep is None:
        pytest.skip("no blocking report found")
    ingest = (rep.get("timing") or {}).get("ingest")
    if not ingest:
        pytest.skip("no ingest timing present")
    for decision in ("ACCEPTABLE","REJECTED"):
        t = ingest.get(decision)
        assert t, f"missing timing for {decision}"
        p95 = float(t.get("p95_ms", 0.0))
        assert p95 <= TARGET_P95_MS, f"p95 too high for {decision}: {p95} > {TARGET_P95_MS}"
