from constitution_scope import evaluate_scope


def test_exact_match():
    out = evaluate_scope(["doc:read"], "doc:read")
    assert out["authorized"] and out["matched_scope"] == "doc:read"


def test_wildcard_segment():
    out = evaluate_scope(["admin:*"], "admin:impersonate")
    assert out["authorized"] and out["matched_scope"] == "admin:*"


def test_resource_hint_suffix():
    out = evaluate_scope(
        ["doc:read:org:123"], "doc:read", resource_scope_hint="org:123"
    )
    assert out["authorized"]


def test_negative_case():
    out = evaluate_scope(["doc:read"], "doc:write")
    assert not out["authorized"] and out["reason_code"] == "scope_miss"
