import types
import sys
import pytest


def test_import_ok_without_env():
    import apps.provenance.driver as d

    assert hasattr(d, "get_driver")


def test_get_driver_missing_env_raises(monkeypatch):
    from apps.provenance import driver as d

    for k in ("NEO4J_URI", "NEO4J_USER", "NEO4J_PASSWORD"):
        monkeypatch.delenv(k, raising=False)
    with pytest.raises(RuntimeError):
        d.get_driver()


def test_get_driver_uses_fake_neo4j(monkeypatch):
    class FakeGraphDatabase:
        calls = []

        @classmethod
        def driver(cls, uri, auth):
            cls.calls.append((uri, auth))
            return object()

    fake = types.SimpleNamespace(GraphDatabase=FakeGraphDatabase)
    sys.modules["neo4j"] = fake

    monkeypatch.setenv("NEO4J_URI", "bolt://fake:7687")
    monkeypatch.setenv("NEO4J_USER", "u")
    monkeypatch.setenv("NEO4J_PASSWORD", "p")

    from apps.provenance import driver as d

    _ = d.get_driver()  # intentionally unused
    assert (
        FakeGraphDatabase.calls and FakeGraphDatabase.calls[-1][0] == "bolt://fake:7687"
    )


def test_apply_startup_schema_calls_apply_constraints(monkeypatch):
    called = {"v": False}

    def fake_apply_constraints(driver):
        called["v"] = True

    import apps.provenance.schema as schema

    monkeypatch.setattr(
        schema, "apply_constraints", fake_apply_constraints, raising=True
    )

    from apps.provenance import driver as d

    d.apply_startup_schema(driver=object())
    assert called["v"] is True
