import os
import pytest
import time
from apps.extractors import text2nkg as nkg

RUN_PERF = os.environ.get("RUN_PERF") in {"1", "true", "yes", "on"}


@pytest.mark.skipif(not RUN_PERF, reason="perf gated by RUN_PERF=1")
def test_perf_micro(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_NKG", "1")
    text = "TP53 inhibits EGFR. BRCA1 binds TP53. EGFR activates RAS. " * 200
    t0 = time.perf_counter()
    edges = nkg.extract(text)
    t1 = time.perf_counter()
    assert len(edges) >= 3
    # generous bound for CI/dev boxes
    assert (t1 - t0) < 0.5
