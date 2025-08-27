import os
import json
import tempfile
import pathlib
import subprocess
import sys


def test_validation_overhead_budget():
    if os.getenv("RUN_PERF", "0") != "1":
        import pytest

        pytest.skip("RUN_PERF=1 to enable perf tests")
    # Run the perf tool once and check the recorded p95 against target (soft check)
    outdir = tempfile.mkdtemp(prefix="perf_")
    env = dict(os.environ)
    env.update(
        {
            "PERF_OUTDIR": outdir,
            "EXTRACTOR_SCI": "0",
            "EXTRACTOR_BIO": "0",
            "EXTRACTOR_TEXT2NKG": "1",
            "TEMPORAL_GRAPH_MODEL": "1",
            "PERF_ITERS": "60",
        }
    )
    cp = subprocess.run(
        [sys.executable, "tools/perf/run_perf.py"],
        env=env,
        capture_output=True,
        text=True,
    )
    assert cp.returncode == 0, cp.stderr
    data = json.loads(pathlib.Path(outdir, "perf_report.json").read_text())
    p95 = data["results"]["validation_overhead"]["latencies_ms"]["p95"]
    # We don't fail hard if slightly above (machines vary); keep headroom generous.
    assert p95 < 170.0 + 50.0, f"validation overhead too high: p95={p95:.2f} ms"
