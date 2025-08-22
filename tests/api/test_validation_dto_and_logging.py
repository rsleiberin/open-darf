from types import SimpleNamespace

from apps.api.dto import to_validation_dto
from apps.constitution_engine import engine
from apps.constitution_engine.phase2 import Decision


def test_to_validation_dto_duck_typing():
    vr = SimpleNamespace(decision=Decision.ALLOW, reason_code="allow_path:granted")
    dto = to_validation_dto(vr)
    assert dto["decision"] == "ALLOW"
    assert dto["reason_code"] == "allow_path:granted"


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


def test_engine_emits_log_line_with_decision_and_reason(caplog):
    caplog.set_level("INFO", logger="constitution_engine")
    ctx = {"principal_id": "p1", "action_id": "a1", "resource_id": "r1"}
    engine.evaluate_request(ctx, FakeSession(True, False))
    blob = " ".join(r.message for r in caplog.records)
    assert "decision=ALLOW" in blob
    assert "reason=" in blob
