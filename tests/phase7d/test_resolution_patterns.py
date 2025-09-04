from pathlib import Path
import os, json
from tools.constitutional.reasoning.resolution_patterns import signature, write_pattern
from tools.constitutional.reasoning.conflict import PrincipleVote, resolve
from tools.constitutional.reasoning.integrate import maybe_enrich_event, record_conflict_pattern

def test_signature_determinism_and_bucketing():
    v = [PrincipleVote("Safety","DENY"), PrincipleVote("sovereignty","allow"), PrincipleVote("safety","deny")]
    sig = signature(v)
    assert sig.startswith("deny:[safety]")
    assert "allow:[sovereignty]" in sig

def test_write_and_integrate_rationale(monkeypatch, tmp_path: Path):
    monkeypatch.setenv("REASONING_PATTERN_PATH", str(tmp_path / "res_pats.jsonl"))
    monkeypatch.setenv("REASONING_ENABLE", "1")
    monkeypatch.setenv("REASONING_PATTERN_WRITE", "1")

    votes = [PrincipleVote("safety","DENY"), PrincipleVote("sovereignty","ALLOW")]
    # direct recording
    pid = record_conflict_pattern(votes, "REJECTED")
    assert pid and pid.startswith("pat:")
    # enrichment should surface 'conflict_rationale' without mutating decision
    base = {"stage":"ingest","id":"doc:pat","decision":"ACCEPTABLE"}
    out = maybe_enrich_event(base, "ACCEPTABLE", ["safety","sovereignty"], "allow provenance-verified", ["doc:pat"], votes=votes)
    assert out["decision"] == "ACCEPTABLE"
    assert "reasoning" in out and "conflict_rationale" in out["reasoning"]
    # file should exist and contain our pattern
    p = tmp_path / "res_pats.jsonl"
    assert p.exists()
    lines = [json.loads(x) for x in p.read_text().splitlines() if x.strip()]
    assert any(x.get("id") == pid for x in lines)
