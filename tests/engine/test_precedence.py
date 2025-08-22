from apps.constitution_engine.precedence import decide_precedence
from apps.constitution_engine.phase2 import Decision


def test_deny_dominates_allow():
    res = decide_precedence(allow_exists=True, deny_exists=True)
    assert res.decision is Decision.DENY
    assert res.reason_code.startswith("deny_precedence")


def test_allow_when_only_allow_exists():
    res = decide_precedence(allow_exists=True, deny_exists=False)
    assert res.decision is Decision.ALLOW
    assert res.reason_code.startswith("allow_path")


def test_indeterminate_when_neither_path_exists():
    res = decide_precedence(allow_exists=False, deny_exists=False)
    assert res.decision is Decision.INDETERMINATE
    assert res.reason_code.startswith("no_policy_match")
