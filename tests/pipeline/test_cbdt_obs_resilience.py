import apps.pipeline.process.cbdt as cbdt  # type: ignore


def _doc():
    return {
        "doc_id": "obs-001",
        "blocks": [{"id": "b1", "text": "clearly undeniable experts say"}],
    }


def test_sink_failure_is_swallowed(monkeypatch):
    monkeypatch.setenv("PIPELINE_CBDT", "1")
    monkeypatch.setenv("PIPELINE_CBDT_PROVIDER", "local")
    monkeypatch.setenv("PIPELINE_PERF", "1")

    # Force the writer to throw
    def boom(*a, **k):
        raise RuntimeError("sink boom")

    monkeypatch.setattr(cbdt, "_safe_write_json", boom, raising=True)

    res = cbdt.cbdt_pass({}, _doc())
    # Should not raise; result should include obs_error signal
    sigs = res.summary.get("signals", [])
    assert any(s.startswith("obs_error:") for s in sigs)
