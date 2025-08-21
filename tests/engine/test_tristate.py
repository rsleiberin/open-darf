import os
from apps.constitution_engine.phase2 import _fail_closed_default, Decision

def test_fail_closed_default_is_indeterminate_when_not_overridden(monkeypatch):
    monkeypatch.delenv("ENGINE_FAIL_OPEN", raising=False)
    res = _fail_closed_default()
    assert res.decision is Decision.INDETERMINATE
    assert res.reason_code.startswith("neo4j_schema_missing")

def test_fail_open_override_allows(monkeypatch):
    monkeypatch.setenv("ENGINE_FAIL_OPEN", "true")
    res = _fail_closed_default()
    assert res.decision is Decision.ALLOW
    assert res.reason_code.startswith("fail_open")
