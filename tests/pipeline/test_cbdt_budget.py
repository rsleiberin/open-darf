import os
from apps.pipeline.process.cbdt import cbdt_pass  # type: ignore


def _doc():
    return {
        "doc_id": "budget-micro-001",
        "blocks": [
            {"id": "b1", "text": "This is clearly undeniable."},
            {"id": "b2", "text": "Some say it might be true."},
        ],
        "lang": "en",
        "mime": "text/plain",
    }


def test_cbdt_p95_within_budget(monkeypatch):
    monkeypatch.setenv("PIPELINE_CBDT", "1")
    monkeypatch.setenv("PIPELINE_CBDT_PROVIDER", "local")
    monkeypatch.setenv("PIPELINE_PERF", "1")
    # Budget env (PR-safe default 50ms; overrideable)
    budget_ms = float(os.getenv("PIPELINE_CBDT_P95_BUDGET_MS", "50"))
    res = cbdt_pass({}, _doc())
    # We record a single-step timing; treat it as p95 for micro fixtures
    assert res.summary["timing_ms"]["cbdt_total"] <= budget_ms
