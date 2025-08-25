from apps import obs
from apps.pipeline.process.cbdt import cbdt_pass


def _doc():
    return {
        "doc_id": "obs-ctr-001",
        "blocks": [
            {"id": "b1", "text": "This is clearly undeniable."},
            {"id": "b2", "text": "Experts say it might be true."},
        ],
        "lang": "en",
        "mime": "text/plain",
    }


def test_cbdt_emits_counters(monkeypatch):
    obs.reset()
    monkeypatch.setenv("PIPELINE_CBDT", "1")
    monkeypatch.setenv("PIPELINE_CBDT_PROVIDER", "local")
    cbdt_pass({}, _doc())
    snap = obs.snapshot()
    assert snap["counters"].get("cbdt.runs", 0) >= 1
    assert snap["counters"].get("cbdt.findings_total", 0) >= 1
    # At least one label counter increments
    label_keys = [k for k in snap["counters"].keys() if k.startswith("cbdt.counts.")]
    assert label_keys, f"no label counters in {snap['counters']}"
    # Histogram recorded
    assert snap["histograms"].get("cbdt.ms", {}).get("n", 0) >= 1
