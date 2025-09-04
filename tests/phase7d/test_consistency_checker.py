from pathlib import Path
import os
from tools.constitutional.reasoning.consistency_checker import check_consistency
from tools.constitutional.reasoning.integrate import record_precedent

def test_consistency_ok(monkeypatch, tmp_path: Path):
    monkeypatch.setenv("REASONING_PRECEDENT_PATH", str(tmp_path / "precedents.jsonl"))
    # seed with ACCEPTABLE for principles set
    record_precedent("prec:a", ["safety","sovereignty"], "allow provenance-verified",)
    # record again with decision stored
    record_precedent("prec:a", ["safety","sovereignty"], "allow provenance-verified",)  # idempotent
    # explicitly write decision using low-level store path (simulate production write)
    from tools.constitutional.reasoning.precedent import LocalPrecedentStore
    s = LocalPrecedentStore(str(tmp_path / "precedents.jsonl"))
    s.upsert("prec:a", ["safety","sovereignty"], "allow provenance-verified", decision="ACCEPTABLE")
    ok, detail = check_consistency("ACCEPTABLE", ["safety","sovereignty"], topk=3)
    assert ok is True
    assert detail["mismatches"] == []

def test_consistency_detects_mismatch(monkeypatch, tmp_path: Path):
    monkeypatch.setenv("REASONING_PRECEDENT_PATH", str(tmp_path / "precedents.jsonl"))
    from tools.constitutional.reasoning.precedent import LocalPrecedentStore
    s = LocalPrecedentStore(str(tmp_path / "precedents.jsonl"))
    s.upsert("prec:x", ["fail-closed"], "empty text", decision="REJECTED")
    ok, detail = check_consistency("ACCEPTABLE", ["fail-closed"], topk=3)
    assert ok is False
    assert detail["mismatches"] and detail["mismatches"][0]["id"] == "prec:x"
