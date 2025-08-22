from apps.constitution_engine.schema.optional_indexes import dry_run


def test_optional_index_dry_run_contains_expected_statements():
    stmts = dry_run()
    assert any("principal_id_idx" in s for s in stmts)
    assert any("node_label_lookup" in s for s in stmts)
    assert any("rel_type_lookup" in s for s in stmts)
