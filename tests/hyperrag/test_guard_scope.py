from apps.hyperrag.guard_scope import guard_call, decide
from apps.constitution_scope.scope import Decision


def test_decide_string_and_bool_variants():
    assert decide("allow")["decision"] is Decision.ALLOW
    assert decide("deny")["decision"] is Decision.DENY
    assert decide("maybe")["decision"] is Decision.INDETERMINATE
    assert decide(True)["decision"] is Decision.ALLOW
    assert decide(False)["decision"] is Decision.DENY


def test_guard_call_allow_executes_and_returns_value():
    ok, val, out = guard_call("allow", lambda x: x + 1, 41)
    assert ok is True and val == 42 and out["decision"] is Decision.ALLOW


def test_guard_call_deny_blocks():
    ok, val, out = guard_call("deny", lambda: 1 / 0)  # would raise if executed
    assert ok is False and val is None and out["decision"] is Decision.DENY


def test_guard_call_indeterminate_blocks_fail_closed():
    ok, val, out = guard_call("unknown-state", lambda: 123)
    assert ok is False and val is None and out["decision"] is Decision.INDETERMINATE


def test_guard_call_callable_rule_with_context():
    def rule(ctx):  # allow if role is "editor"
        return {
            "decision": "ALLOW" if ctx.get("role") == "editor" else "DENY",
            "reason": "role-check",
        }

    ok, val, out = guard_call(rule, lambda: "ok", context={"role": "editor"})
    assert ok is True and val == "ok" and out["decision"] is Decision.ALLOW
    ok2, val2, out2 = guard_call(rule, lambda: "nope", context={"role": "viewer"})
    assert ok2 is False and val2 is None and out2["decision"] is Decision.DENY
