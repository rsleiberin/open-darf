from apps.constitution_engine.schema import init as m


def test_scope_indexes_present():
    steps = getattr(m, "SCHEMA_STEPS", [])
    # Principal scopes index
    assert any("Principal" in s and "p.scopes" in s for s in steps)
    # Action required_scope index
    assert any("Action" in s and "a.required_scope" in s for s in steps)
