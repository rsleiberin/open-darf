import pytest
from apps.extractors import biobert


def test_disabled_raises(monkeypatch):
    monkeypatch.delenv("EXTRACTOR_BIO", raising=False)
    with pytest.raises(RuntimeError):
        biobert.extract("EGFR and cancer.")


def test_disambiguation_prefers_gene(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_BIO", "1")
    assert biobert.disambiguate("EGFR") == "GENE_SYMBOL"
    assert biobert.disambiguate("cancer") == "DISEASE"
    g, d = biobert.candidate_labels_for("EGFR")
    assert g and not d


def test_basic_entities(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_BIO", "1")
    text = "PMID: 99999 reports EGFR in glioblastoma; treat with aspirin."
    ents = biobert.extract(text)
    labels = {e.label for e in ents}
    assert {"PMID", "GENE_SYMBOL", "DISEASE", "DRUG"} <= labels
    assert any(e.text.lower() == "aspirin" and e.label == "DRUG" for e in ents)
