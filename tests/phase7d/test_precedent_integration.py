from pathlib import Path
from tools.constitutional.reasoning.integrate import (
    maybe_enrich_event, record_precedent
)
import os

def test_precedent_citation_enabled(monkeypatch, tmp_path: Path):
    # enable enrichment + local path
    monkeypatch.setenv("REASONING_ENABLE", "1")
    monkeypatch.setenv("REASONING_PRECEDENT_PATH", str(tmp_path / "precedents.jsonl"))
    monkeypatch.setenv("REASONING_PRECEDENT_WRITE", "1")

    # seed two precedents
    record_precedent("prec:one", ["safety","sovereignty"], "block unsafe inputs")
    record_precedent("prec:two", ["transparency"], "emit audit trail")

    # now enrich for a matching principles set
    base = {"stage": "ingest", "id": "doc:42"}
    out = maybe_enrich_event(base, "ACCEPTABLE", ["safety","sovereignty"], "allow provenance-verified", ["doc:42"])
    assert "reasoning" in out
    cited = out["reasoning"]["cited_precedents"]
    assert isinstance(cited, list) and len(cited) >= 1
    assert "prec:one" in cited

def test_precedent_enrichment_disabled(monkeypatch, tmp_path: Path):
    monkeypatch.setenv("REASONING_ENABLE", "0")
    monkeypatch.setenv("REASONING_PRECEDENT_PATH", str(tmp_path / "precedents.jsonl"))
    base = {"stage": "ingest", "id": "doc:99"}
    out = maybe_enrich_event(base, "REJECTED", ["fail-closed"], "empty text", ["doc:99"])
    assert "reasoning" not in out
