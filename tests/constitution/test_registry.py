import pytest
from apps.constitution_scope import registry as reg


def dummy_allow(*_args, **_kwargs) -> str:
    return "ALLOW"


def dummy_deny(*_args, **_kwargs) -> str:
    return "DENY"


def test_register_and_get_on_instance() -> None:
    local = reg.RuleRegistry()
    local.register("role:editor", dummy_allow)
    assert local.has("role:editor")
    fn = local.get("role:editor")
    assert callable(fn)
    assert fn({}) == "ALLOW"
    assert "role:editor" in local.names()


def test_duplicate_registration_raises() -> None:
    local = reg.RuleRegistry()
    local.register("x", dummy_deny)
    with pytest.raises(KeyError):
        local.register("x", dummy_allow)


def test_unknown_rule_raises() -> None:
    local = reg.RuleRegistry()
    with pytest.raises(KeyError):
        local.get("missing")


def test_singleton_helpers_work_and_are_idempotent() -> None:
    name = "test:helper-rule"
    if not reg.has(name):
        reg.register(name, dummy_allow)
    assert reg.has(name)
    assert callable(reg.get(name))
    assert reg.get(name)({}) == "ALLOW"
