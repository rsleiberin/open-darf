from apps.constitution_engine import engine
from apps.constitution_engine.phase2 import Decision


def mkctx():
    return {"principal_id": "p1", "action_id": "a1", "resource_id": "r1"}


class _Result:
    def __init__(self, rec):
        self._rec = rec

    def single(self):
        return self._rec


class FakeSession:
    def __init__(self, allow_exists: bool, deny_exists: bool):
        self.allow_exists = allow_exists
        self.deny_exists = deny_exists

    def run(self, *_a, **_k):
        return _Result(
            {"allow_exists": self.allow_exists, "deny_exists": self.deny_exists}
        )


def test_allow_when_allow_and_no_deny():
    vr = engine.evaluate_request(mkctx(), FakeSession(True, False))
    assert vr.decision == Decision.ALLOW


def test_deny_precedence_when_both():
    vr = engine.evaluate_request(mkctx(), FakeSession(True, True))
    assert vr.decision == Decision.DENY


def test_indeterminate_when_neither():
    vr = engine.evaluate_request(mkctx(), FakeSession(False, False))
    assert vr.decision == Decision.INDETERMINATE


class BoomSession:
    def run(self, *_a, **_k):
        raise RuntimeError("db down")


def test_fail_closed_default_on_db_error(monkeypatch):
    monkeypatch.delenv("ENGINE_FAIL_OPEN", raising=False)
    vr = engine.evaluate_request(mkctx(), BoomSession())
    assert vr.decision in (Decision.INDETERMINATE, Decision.DENY)


def test_dev_override_fail_open(monkeypatch):
    monkeypatch.setenv("ENGINE_FAIL_OPEN", "true")
    vr = engine.evaluate_request(mkctx(), BoomSession())
    assert vr.decision == Decision.ALLOW
