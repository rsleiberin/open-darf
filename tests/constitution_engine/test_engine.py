import pytest
from apps.constitution_engine.engine import ConstraintEngine


def test_missing_keys_disallowed():
    eng = ConstraintEngine()
    res = eng.validate({"action": "read"})
    assert res.allowed is False
    assert "missing" in ",".join(res.reasons)


@pytest.mark.parametrize(
    "action,allowed", [("read", True), ("delete_system", False), ("grant_root", False)]
)
def test_baseline_actions(action, allowed):
    eng = ConstraintEngine()
    res = eng.validate({"principal": "u:1", "action": action, "resource": "doc:1"})
    assert res.allowed is allowed


def test_bench_runs_without_neo4j(monkeypatch):
    # Ensure no env required
    monkeypatch.delenv("NEO4J_URI", raising=False)
    monkeypatch.delenv("NEO4J_USER", raising=False)
    monkeypatch.delenv("NEO4J_PASSWORD", raising=False)
    eng = ConstraintEngine()
    res = eng.validate({"principal": "u:1", "action": "read", "resource": "doc:1"})
    assert res.allowed is True
