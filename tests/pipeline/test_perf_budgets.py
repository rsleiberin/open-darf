import json
import os
import pathlib
from apps.pipeline.ingest.local import LocalFSIngest
from apps.pipeline.run import run_once


def test_perf_budgets_p95(tmp_path, monkeypatch):
    root = tmp_path / "in"
    root.mkdir(parents=True, exist_ok=True)
    (root / "a.txt").write_text("a" * 10)
    (root / "b.txt").write_text("b" * 10)
    monkeypatch.setenv("PIPELINE_PERF", "1")
    count, path = run_once(LocalFSIngest(str(root)), bucket="pipeline_budget")
    data = json.loads(pathlib.Path(path).read_text())
    # Budget (ms): keep conservative for CI jitter
    parse_budget = float(os.getenv("PIPELINE_PARSE_P95_BUDGET_MS", "25"))
    proc_budget = float(os.getenv("PIPELINE_PROCESS_P95_BUDGET_MS", "25"))
    assert data["perf"]["parse_ms"]["p95"] <= parse_budget
    assert data["perf"]["process_ms"]["p95"] <= proc_budget
