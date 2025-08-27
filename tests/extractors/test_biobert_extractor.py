from apps.extractors.biobert_extractor import BioBERTExtractor
from apps.knowledge_graph.entity_extraction import extract_all


def test_bio_disabled_safe(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_BIO", "0")
    out = BioBERTExtractor().extract("aspirin reduces fever")
    assert out["entities"] == []
    assert out["reason_code"] == "disabled"


def test_bio_empty_text_denied(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_BIO", "1")
    out = BioBERTExtractor().extract("  ")
    assert out["decision"] == "DENY"
    assert out["reason_code"] == "empty_text"


def test_aggregator_no_extractors(monkeypatch):
    monkeypatch.delenv("EXTRACTOR_SCI", raising=False)
    monkeypatch.delenv("EXTRACTOR_BIO", raising=False)
    out = extract_all("BRCA1 mutation is implicated in cancer")
    assert out["decision"] == "INDETERMINATE"
    assert out["entities"] == []
