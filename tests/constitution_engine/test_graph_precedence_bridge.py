# SPDX-License-Identifier: MIT
import importlib
import pytest

MOD_PATH = "constitution_engine.graph_precedence_bridge"


@pytest.fixture(autouse=True)
def _clean_env(monkeypatch):
    for k in ("GRAPH_PRECEDENCE",):
        monkeypatch.delenv(k, raising=False)


def _reload():
    return importlib.reload(importlib.import_module(MOD_PATH))


def test_allow_overrides(monkeypatch):
    m = _reload()

    def fake_eval(session, p, a, r):
        return {"decision": "ALLOW", "reason_code": "allow_path"}

    monkeypatch.setattr(m, "evaluate_precedence_from_graph", fake_eval)
    assert m.resolve_via_graph("u", "act", "res", object()) == ("ALLOW", "allow_path")


def test_deny_overrides(monkeypatch):
    m = _reload()

    def fake_eval(session, p, a, r):
        return {"decision": "DENY", "reason_code": "deny_path"}

    monkeypatch.setattr(m, "evaluate_precedence_from_graph", fake_eval)
    assert m.resolve_via_graph("u", "act", "res", object()) == ("DENY", "deny_path")


def test_indeterminate_no_override(monkeypatch):
    m = _reload()

    def fake_eval(session, p, a, r):
        return {"decision": "INDETERMINATE", "reason_code": "meh"}

    monkeypatch.setattr(m, "evaluate_precedence_from_graph", fake_eval)
    assert m.resolve_via_graph("u", "a", "r", object()) is None


def test_adapter_error_no_override(monkeypatch):
    m = _reload()

    def boom(*_a, **_k):
        raise RuntimeError("adapter failed")

    monkeypatch.setattr(m, "evaluate_precedence_from_graph", boom)
    assert m.resolve_via_graph("u", "a", "r", object()) is None


def test_flag_off_unused():
    m = _reload()
    assert m.should_use_graph_precedence() is False


@pytest.mark.parametrize("val", ["1", "true", "on", "YES", " TrUe "])
def test_flag_on_variants(monkeypatch, val):
    m = _reload()
    monkeypatch.setenv("GRAPH_PRECEDENCE", val)
    assert m.should_use_graph_precedence() is True
