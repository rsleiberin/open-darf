import os
from tools.constitutional.reasoning.integrate import maybe_enrich_event

def _mk(base_id, enable):
    os.environ["REASONING_ENABLE"] = "1" if enable else "0"
    base = {"stage":"ingest","id":base_id,"decision":"ACCEPTABLE"}
    out = maybe_enrich_event(base, "ACCEPTABLE", ["safety"], "allow", [base_id])
    return out

def test_invariance_fields_and_decision():
    off = _mk("doc:off", False)
    on  = _mk("doc:on", True)
    # Decisions unchanged (we don't alter decision field)
    assert off.get("decision") == "ACCEPTABLE"
    assert on.get("decision")  == "ACCEPTABLE"
    # Enrichment present only when enabled, and additive (non-breaking)
    assert "reasoning" not in off
    assert "reasoning" in on
    # Base fields preserved
    for k in ("stage","id","decision"):
        assert k in on and k in off
