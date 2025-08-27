import os
import json
import tempfile
import pathlib
import subprocess
import sys


def test_perf_runner_gated():
    if os.getenv("RUN_PERF", "0") != "1":
        import pytest

        pytest.skip("RUN_PERF=1 to enable perf tests")
    outdir = tempfile.mkdtemp(prefix="perf_")
    env = dict(os.environ)
    env["PERF_OUTDIR"] = outdir
    cmd = [sys.executable, "tools/perf/run_perf.py"]
    cp = subprocess.run(cmd, env=env, capture_output=True, text=True)
    assert cp.returncode == 0, cp.stderr
    report = pathlib.Path(outdir, "perf_report.json")
    assert report.exists(), "perf_report.json not created"
    data = json.loads(report.read_text())
    # Sanity: keys exist
    assert "results" in data and "hybrid_e2e" in data["results"]
