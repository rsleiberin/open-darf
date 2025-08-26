from typing import Any, Dict, List
from apps.constitution_scope.scope import Decision, evaluate
from apps.hyperrag.guard_scope import guard_call
from apps.hyperrag.guarded_store_scope import GuardedStoreScope


# Minimal in-memory store used across acceptance cases
class _Store:
    def __init__(self) -> None:
        self._d: Dict[Any, Any] = {}

    def put(self, k: Any, v: Any) -> bool:
        self._d[k] = v
        return True

    def get(self, k: Any) -> Any:
        return self._d.get(k)

    def __contains__(self, k: Any) -> bool:
        return k in self._d


def test_acceptance_tri_state_decision_surface():
    # Literal forms
    assert evaluate("allow")["decision"] is Decision.ALLOW
    assert evaluate("deny")["decision"] is Decision.DENY
    assert evaluate("unknown")["decision"] is Decision.INDETERMINATE

    # Callable with context
    def role_rule(ctx):
        return {
            "decision": "ALLOW" if ctx.get("role") == "editor" else "DENY",
            "reason": "role-check",
        }

    out_editor = evaluate(role_rule, {"role": "editor"})
    out_viewer = evaluate(role_rule, {"role": "viewer"})
    assert out_editor["decision"] is Decision.ALLOW
    assert out_viewer["decision"] is Decision.DENY


def test_acceptance_guard_exec_paths_and_audit():
    audits: List[dict] = []
    store = _Store()
    # Allow path
    gs = GuardedStoreScope(store, "allow", audit_emit=audits.append)
    ok = gs.put("k1", {"id": 1}, context={"role": "editor"})
    assert ok is True and "k1" in store
    last = audits[-1]
    assert (
        last["op"] == "put"
        and last["ok"] is True
        and last["decision"]["decision"] is Decision.ALLOW
    )

    # Deny path
    gs_deny = GuardedStoreScope(store, "deny", audit_emit=audits.append)
    ok2 = gs_deny.put("k2", {"id": 2})
    assert ok2 is False and "k2" not in store
    last = audits[-1]
    assert (
        last["op"] == "put"
        and last["ok"] is False
        and last["decision"]["decision"] is Decision.DENY
    )

    # Indeterminate (fail-closed)
    gs_indet = GuardedStoreScope(store, "??", audit_emit=audits.append)
    ok3 = gs_indet.put("k3", {"id": 3})
    assert ok3 is False and "k3" not in store
    assert audits[-1]["decision"]["decision"] is Decision.INDETERMINATE


def test_acceptance_guard_call_end_to_end_callable_rule():
    def rule(ctx):
        return {
            "decision": "ALLOW" if ctx.get("role") == "editor" else "DENY",
            "reason": "role-check",
        }

    ok, val, out = guard_call(rule, lambda x: x * 2, 21, context={"role": "editor"})
    assert ok is True and val == 42 and out["decision"] is Decision.ALLOW

    ok2, val2, out2 = guard_call(rule, lambda: "nope", context={"role": "viewer"})
    assert ok2 is False and val2 is None and out2["decision"] is Decision.DENY


def test_acceptance_audit_sink_resilience():
    # Audit sink exceptions must never break writes on ALLOW
    def boom(_evt):  # pragma: no cover - behavior validated by not raising
        raise RuntimeError("sink failed")

    store = _Store()
    gs = GuardedStoreScope(store, "allow", audit_emit=boom)
    assert gs.put("safe", 1) is True and "safe" in store
