from apps.extractors.scibert_extractor import SciBERTExtractor
from apps.guards.constitutional import precedence


def test_disabled_is_safe(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_SCI", "0")
    ex = SciBERTExtractor()
    out = ex.extract("science works")
    assert out["reason_code"] == "disabled"
    assert out["entities"] == []
    assert out["decision"] in ("ALLOW", "INDETERMINATE")


def test_empty_text_denied(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_SCI", "1")
    ex = SciBERTExtractor()
    out = ex.extract("   ")
    assert out["decision"] == "DENY"
    assert out["reason_code"] == "empty_text"


def test_precedence_order():
    assert precedence("DENY", "ALLOW") == "DENY"
    assert precedence("INDETERMINATE", "ALLOW") == "INDETERMINATE"
    assert precedence("DENY", "INDETERMINATE") == "DENY"
