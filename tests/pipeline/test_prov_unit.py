from apps.pipeline.prov import prov_pass


def _doc(doc_id="prov-001"):
    return {
        "doc_id": doc_id,
        "blocks": [{"id": "b1", "text": "hello world"}],
        "lang": "en",
        "mime": "text/plain",
    }


def test_prov_flag_off(monkeypatch):
    monkeypatch.delenv("PIPELINE_PROV", raising=False)
    res = prov_pass({}, _doc())
    assert res.jsonld == {}


def test_prov_flag_on_shape_and_receipt(monkeypatch):
    monkeypatch.setenv("PIPELINE_PROV", "1")
    monkeypatch.setenv("PIPELINE_PERF", "1")
    r = prov_pass({}, _doc("prov-shape-001"))
    j = r.jsonld
    assert j.get("@context"), "missing @context"
    assert "entity" in j and "activity" in j and "agent" in j
    assert r.receipt_path is not None
    assert r.timing_ms >= 0.0
