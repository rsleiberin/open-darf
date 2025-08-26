from apps.constitution_scope.scope import Decision, evaluate, coerce_decision


def test_bool_true_false():
    assert evaluate(True)["decision"] is Decision.ALLOW
    assert evaluate(False)["decision"] is Decision.DENY


def test_string_variants():
    assert evaluate("allow")["decision"] is Decision.ALLOW
    assert evaluate("DENIED")["decision"] is Decision.DENY
    assert evaluate("maybe")["decision"] is Decision.INDETERMINATE
    assert evaluate("weird")["decision"] is Decision.INDETERMINATE


def test_dict_decision_and_allow():
    assert evaluate({"decision": "allow", "reason": "ok"})["decision"] is Decision.ALLOW
    assert evaluate({"allow": False, "reason": "nope"})["decision"] is Decision.DENY
    # unknown dict shape -> indeterminate
    out = evaluate({"foo": "bar"})
    assert out["decision"] is Decision.INDETERMINATE and out["allow"] is None


def test_tuple_shapes():
    assert evaluate((True, "bool-ok"))["decision"] is Decision.ALLOW
    assert evaluate(("deny", "nope"))["decision"] is Decision.DENY
    assert evaluate(("???", "huh"))["decision"] is Decision.INDETERMINATE


def test_callable_and_fail_closed():
    def rule_ok(ctx):
        return {"decision": "ALLOW", "reason": f"user:{ctx.get('u')}"}

    def rule_boom(ctx):
        raise RuntimeError("bad")

    ok = evaluate(rule_ok, {"u": "alice"})
    assert ok["decision"] is Decision.ALLOW and "user:alice" in ok["reason"]

    boom = evaluate(rule_boom, {})
    assert boom["decision"] is Decision.INDETERMINATE and boom["allow"] is None


def test_coerce_never_raises():
    for v in (object(), 123, 12.3, ["x"], ("x", 1, {}), None):
        out = coerce_decision(v)  # must not raise
        assert out["decision"] in (
            Decision.ALLOW,
            Decision.DENY,
            Decision.INDETERMINATE,
        )
