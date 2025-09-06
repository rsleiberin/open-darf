from scripts.phase7f.tri_state import Decision, combine_decisions, fail_closed, decide_with_constraints

def test_deny_precedence():
    assert combine_decisions([Decision.ALLOW, Decision.DENY, Decision.ALLOW]) == Decision.DENY
    assert combine_decisions([Decision.ALLOW, Decision.ALLOW]) == Decision.ALLOW
    assert combine_decisions([Decision.ALLOW, Decision.INDETERMINATE]) == Decision.INDETERMINATE

def test_fail_closed_semantics():
    assert fail_closed(True, True) == Decision.ALLOW
    assert fail_closed(True, None) == Decision.INDETERMINATE
    assert fail_closed(True, False) == Decision.DENY

def test_decide_with_constraints_examples():
    scores = {"docA":0.9}
    d, info = decide_with_constraints(scores, {"safety_ok": True, "policy_ok": True})
    assert d == Decision.ALLOW
    d, info = decide_with_constraints(scores, {"safety_ok": True, "policy_ok": None})
    assert d == Decision.INDETERMINATE
    d, info = decide_with_constraints(scores, {"safety_ok": True, "policy_ok": False})
    assert d == Decision.DENY
