from constitution_graph.precedence_adapter import evaluate_precedence_from_graph


class FakeTx:
    def __init__(self, records):
        self._records = records

    def run(self, cypher, **params):
        return self._records


class FakeSession:
    def __init__(self, records):
        self._records = records

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        return False

    def read_transaction(self, fn):
        return fn(FakeTx(self._records))


class FakeDriver:
    def __init__(self, records):
        self._records = records

    def session(self):
        return FakeSession(self._records)


def dp(allow_exists, deny_exists):
    if deny_exists:
        return "DENY", "deny_precedence"
    if allow_exists:
        return "ALLOW", "allow_present_no_deny"
    return "INDETERMINATE", "no_allow_no_deny"


def test_adapter_allow_only():
    drv = FakeDriver([{"allow_exists": True, "deny_exists": False}])
    out = evaluate_precedence_from_graph(drv, "p", "a", "r", decide_precedence_fn=dp)
    assert out["decision"] == "ALLOW"
    assert out["allow_exists"] is True and out["deny_exists"] is False
    assert out["reason_code"] == "allow_present_no_deny"


def test_adapter_deny_only():
    drv = FakeDriver([{"allow_exists": False, "deny_exists": True}])
    out = evaluate_precedence_from_graph(drv, "p", "a", "r", decide_precedence_fn=dp)
    assert out["decision"] == "DENY"
    assert out["allow_exists"] is False and out["deny_exists"] is True
    assert out["reason_code"] == "deny_precedence"


def test_adapter_mixed_short_circuit():
    drv = FakeDriver(
        [
            {"allow_exists": False, "deny_exists": False},
            {"allow_exists": True, "deny_exists": False},
            {"allow_exists": False, "deny_exists": True},
        ]
    )
    out = evaluate_precedence_from_graph(drv, "p", "a", "r", decide_precedence_fn=dp)
    assert out["decision"] == "DENY"  # final deny wins on resolver logic
    assert out["allow_exists"] is True and out["deny_exists"] is True


def test_adapter_error_fail_closed():
    class BadDriver:
        def session(self):
            raise RuntimeError("no graph")

    out = evaluate_precedence_from_graph(
        BadDriver(), "p", "a", "r", decide_precedence_fn=dp
    )
    assert out["decision"] == "INDETERMINATE"
    assert out["reason_code"] == "graph_query_error"
