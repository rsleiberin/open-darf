from constitution_graph.neo4j_allow_deny import (
    parse_allow_deny,
    build_allow_deny_cypher,
)


def test_parse_allow_deny_empty():
    assert parse_allow_deny([]) == (False, False)


def test_parse_allow_deny_allow_only():
    recs = [{"allow_exists": True, "deny_exists": False}]
    assert parse_allow_deny(recs) == (True, False)


def test_parse_allow_deny_deny_only():
    recs = [{"allow_exists": False, "deny_exists": True}]
    assert parse_allow_deny(recs) == (False, True)


def test_parse_allow_deny_mixed_multiple_records():
    recs = [
        {"allow_exists": False, "deny_exists": False},
        {"allow_exists": True},
        {"deny_exists": True},
    ]
    assert parse_allow_deny(recs) == (True, True)


def test_parse_allow_deny_missing_keys_defaults_false():
    recs = [{}]
    assert parse_allow_deny(recs) == (False, False)


def test_build_query_tokens_present():
    q = build_allow_deny_cypher()
    assert isinstance(q, str)
    for token in ("$principal_id", "$action_id", "$resource_id", "ALLOW", "DENY"):
        assert token in q
