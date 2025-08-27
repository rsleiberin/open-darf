from apps.extractors.text2nkg_extractor import Text2NKGExtractor
from apps.knowledge_graph.entity_extraction import extract_all


def test_text2nkg_disabled_safe(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_TEXT2NKG", "0")
    out = Text2NKGExtractor().extract("AI enables research.")
    assert out["reason_code"] == "disabled"
    assert out["relations"] == []


def test_text2nkg_simple_relation(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_TEXT2NKG", "1")
    out = Text2NKGExtractor().extract("Vitamin C prevents scurvy.")
    assert out["decision"] in ("ALLOW", "INDETERMINATE")
    assert out["relations"], "should detect at least one relation"
    rel = out["relations"][0]
    assert rel["relation"] == "prevents"
    role_names = {r["name"] for r in rel["roles"]}
    assert {"subject", "predicate", "object"}.issubset(role_names)


def test_orchestrator_relations_path(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_SCI", "0")
    monkeypatch.setenv("EXTRACTOR_BIO", "0")
    monkeypatch.setenv("EXTRACTOR_TEXT2NKG", "1")
    out = extract_all("System uses database.")
    assert (
        "relations" in out and out["relations"]
    ), "orchestrator should surface relations"
