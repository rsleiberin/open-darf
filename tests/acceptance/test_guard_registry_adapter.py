from apps.constitution_scope import registry as reg
from apps.hyperrag.guard_registry_adapter import decide_with_rule


def _allow(*_args, **_kwargs) -> str:
    return "ALLOW"


def _indet(*_args, **_kwargs) -> str:
    return "INDETERMINATE"


def test_decide_with_rule_by_name_allows():
    if not reg.has("t:allow"):
        reg.register("t:allow", _allow)
    assert decide_with_rule("t:allow", {}) == "ALLOW"


def test_decide_with_rule_callable_indeterminate():
    assert decide_with_rule(_indet, {}) == "INDETERMINATE"


def test_unknown_rule_fails_closed_to_deny():
    assert decide_with_rule("t:missing", {}) == "DENY"
