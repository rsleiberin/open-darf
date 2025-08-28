from apps.knowledge_graph.entity_extraction import extract_all


def test_extract_all_flags_off(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_SCI", "0")
    monkeypatch.setenv("EXTRACTOR_BIO", "0")
    monkeypatch.setenv("EXTRACTOR_TEXT2NKG", "0")
    out = extract_all("Aspirin reduces fever and inflammation.")
    assert out["decision"] == "INDETERMINATE"
    assert isinstance(out["entities"], list)
    assert isinstance(out["relations"], list)
    assert isinstance(out["temporals"], list)
    # Expect traces for each extractor indicating skipped/flag_off
    comps = [t.get("component") for t in out["guard_trace"] if isinstance(t, dict)]
    assert "scibert" in comps and "biobert" in comps and "text2nkg" in comps
