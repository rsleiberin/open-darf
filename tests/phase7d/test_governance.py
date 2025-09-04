import json
from pathlib import Path
from tools.constitutional.reasoning.governance import load, filter_precedents, maybe_override_decision
from tools.constitutional.reasoning.integrate import cite_precedents, record_precedent
from tools.constitutional.reasoning.consistency_checker import check_consistency
from tools.constitutional.reasoning.precedent import LocalPrecedentStore

def test_deprecation_and_override(monkeypatch, tmp_path: Path):
    # Configure governance: deprecate prec:two and override decision for safety|sovereignty -> REJECTED
    gov = {
        "deprecate": ["prec:two"],
        "principle_overrides": {"safety|sovereignty": "REJECTED"}
    }
    monkeypatch.setenv("REASONING_GOVERNANCE_JSON", json.dumps(gov))
    monkeypatch.setenv("REASONING_PRECEDENT_PATH", str(tmp_path / "precedents.jsonl"))
    # Seed precedents
    s = LocalPrecedentStore(str(tmp_path / "precedents.jsonl"))
    s.upsert("prec:one", ["safety","sovereignty"], "allow provenance-verified", decision="ACCEPTABLE")
    s.upsert("prec:two", ["safety"], "legacy rule", decision="REJECTED")
    # record_precedent respects deprecation (no write for deprecated)
    record_precedent("prec:two", ["safety"], "legacy rule again")  # should be a no-op
    # cite should filter out deprecated
    c = cite_precedents(["safety"], topk=5)
    assert "prec:two" not in c
    # override flips proposed decision; consistency check reflects governance_applied
    ok, detail = check_consistency("ACCEPTABLE", ["safety","sovereignty"], topk=3)
    assert detail["governance_applied"] is True
    assert detail["proposed"] == "REJECTED"
    assert ok is False  # because previous precedent was ACCEPTABLE
