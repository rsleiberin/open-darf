from apps.pipeline.oscar import oscar_pass


def _doc(doc_id="oscar-001"):
    return {
        "doc_id": doc_id,
        "blocks": [{"id": "b1", "text": "Clearly, experts say it might be true."}],
    }


def test_oscar_flag_off(monkeypatch):
    monkeypatch.delenv("PIPELINE_OSCAR", raising=False)
    res = oscar_pass({}, _doc())
    assert res.risk_score == 0.0 and res.tags == []


def test_oscar_flag_on_receipt(monkeypatch):
    monkeypatch.setenv("PIPELINE_OSCAR", "1")
    monkeypatch.setenv("PIPELINE_PERF", "1")
    r = oscar_pass({}, _doc("oscar-shape-001"))
    assert r.risk_score > 0.0
    assert r.receipt_path is not None
