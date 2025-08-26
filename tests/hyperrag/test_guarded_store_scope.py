from typing import Dict, Any, List
from apps.hyperrag.guarded_store_scope import GuardedStoreScope
from apps.constitution_scope.scope import Decision


class DummyStore:
    def __init__(self):
        self.data: Dict[Any, Any] = {}

    def put(self, key, value):
        self.data[key] = value
        return True

    def get(self, key):
        return self.data.get(key)

    def __contains__(self, key):
        return key in self.data


def test_allow_writes_and_emits_audit():
    store = DummyStore()
    audits: List[dict] = []
    gs = GuardedStoreScope(store, "allow", audit_emit=audits.append)

    ok = gs.put("k", 1, context={"role": "editor"})
    assert ok is True
    assert "k" in store and store.get("k") == 1
    assert audits and audits[-1]["op"] == "put"
    assert audits[-1]["decision"]["decision"] is Decision.ALLOW
    assert audits[-1]["ok"] is True


def test_deny_blocks_write_and_emits_audit():
    store = DummyStore()
    audits: List[dict] = []
    gs = GuardedStoreScope(store, "deny", audit_emit=audits.append)

    ok = gs.put("k", 1)
    assert ok is False
    assert "k" not in store
    assert audits and audits[-1]["decision"]["decision"] is Decision.DENY
    assert audits[-1]["ok"] is False


def test_indeterminate_blocks_fail_closed():
    store = DummyStore()
    audits: List[dict] = []
    gs = GuardedStoreScope(store, "unknown", audit_emit=audits.append)

    ok = gs.put("k", 1)
    assert ok is False
    assert "k" not in store
    assert audits[-1]["decision"]["decision"] is Decision.INDETERMINATE


def test_callable_rule_uses_context():
    def rule(ctx):
        return {
            "decision": "ALLOW" if ctx.get("role") == "editor" else "DENY",
            "reason": "role-check",
        }

    store = DummyStore()
    audits: List[dict] = []
    gs = GuardedStoreScope(store, rule, audit_emit=audits.append)

    assert gs.put("a", 1, context={"role": "editor"}) is True
    assert "a" in store

    assert gs.put("b", 2, context={"role": "viewer"}) is False
    assert "b" not in store


def test_audit_sink_never_breaks_flow_on_error():
    def boom(_evt):
        raise RuntimeError("sink failed")

    store = DummyStore()
    gs = GuardedStoreScope(store, "allow", audit_emit=boom)
    # Even if audit sink explodes, the write should still succeed.
    assert gs.put("z", 9) is True
    assert "z" in store
