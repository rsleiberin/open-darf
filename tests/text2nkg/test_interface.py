import pytest
from apps.extractors import text2nkg as nkg


def test_disabled(monkeypatch):
    monkeypatch.delenv("EXTRACTOR_NKG", raising=False)
    with pytest.raises(RuntimeError):
        nkg.extract("TP53 inhibits EGFR.")


def test_simple_edges(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_NKG", "1")
    text = "TP53 inhibits EGFR. BRCA1 binds TP53. EGFR activates RAS."
    edges = nkg.extract(text)
    rels = {e.relation for e in edges}
    assert {"INHIBITS", "BINDS", "ACTIVATES"} <= rels
    assert any(
        e.head == "TP53" and e.relation == "INHIBITS" and e.tail == "EGFR"
        for e in edges
    )
    assert all(nkg.validate(e) for e in edges)


def test_validation(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_NKG", "1")
    from apps.extractors.text2nkg import Hyperedge, validate

    assert validate(Hyperedge("A", "BINDS", "B"))
    assert not validate(Hyperedge("", "BINDS", "B"))
    assert not validate(Hyperedge("A", "UNKNOWN", "B"))
