import os
from apps.pipeline.anchors import anchors_pass


def test_anchors_within_budget(monkeypatch):
    monkeypatch.setenv("PIPELINE_ANCHORS", "1")
    monkeypatch.delenv("PIPELINE_ANCHORS_SUB", raising=False)
    budget_ms = float(os.getenv("PIPELINE_ANCHOR_P95_BUDGET_MS", "50"))
    # moderately sized text
    text = "lorem ipsum " * 2000
    res = anchors_pass({}, {"doc_id": "bench1", "blocks": [{"id": "b1", "text": text}]})
    elapsed = res.timing_ms
    assert elapsed <= budget_ms
