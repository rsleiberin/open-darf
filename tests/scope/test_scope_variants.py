from apps.constitution_scope.scope import evaluate, parse_grants


def test_negative_precedence_simple():
    assert evaluate("doc:write", ["doc:write", "-doc:write"]) == "DENY"


def test_hierarchical_allow_prefix():
    # org:123 allows deeper resources
    assert evaluate("org:123:project:7", ["org:123"]) == "ALLOW"


def test_hierarchical_wildcard():
    assert evaluate("org:987:team:5", ["org:*"]) == "ALLOW"


def test_no_match_is_indeterminate():
    assert evaluate("billing:read", ["doc:write", "org:1"]) == "INDETERMINATE"


def test_negative_beats_wildcard_allow():
    assert evaluate("org:42:project:9", ["org:*", "-org:42"]) == "DENY"


def test_parse_grants_splits_pos_neg():
    pos, neg = parse_grants(["a:b", "-c:d", "e:*", "-f"])
    assert "a:b" in pos and "e:*" in pos and "c:d" in neg and "f" in neg
