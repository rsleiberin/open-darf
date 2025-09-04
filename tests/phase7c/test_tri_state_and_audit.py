from tools.constitutional.tri_state import TriState
from tools.constitutional.audit import AuditEvent

def test_tristate_roundtrip():
    assert TriState.from_str("acceptable") == TriState.ACCEPTABLE
    assert TriState.from_str("REJECTED") == TriState.REJECTED
    assert TriState.from_str("Pending") == TriState.PENDING

def test_audit_shape():
    ev = AuditEvent(doc_id="x", stage="ingest", decision=TriState.ACCEPTABLE, rule_id="R1", rationale="ok")
    d = ev.to_dict()
    assert d["doc_id"] == "x"
    assert d["decision"] == "ACCEPTABLE"
    assert d["stage"] == "ingest"
