import pytest
from apps.extractors import biobert


@pytest.mark.skipif(False, reason="service-free acceptance")
def test_acceptance_biobert_smoke(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_BIO", "1")
    text = "EGFR mutation in cancer; PMID: 123."
    ents = biobert.extract(text)
    assert any(e.label == "GENE_SYMBOL" for e in ents)
    assert any(e.label == "DISEASE" for e in ents)
