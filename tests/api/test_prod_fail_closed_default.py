import os
from apps.api.adapter import validate


class ErrorSession:
    def run(self, *a, **k):
        raise RuntimeError("boom")


def test_prod_env_ignores_engine_fail_open(monkeypatch):
    # Simulate production environment AND mistakenly set ENGINE_FAIL_OPEN=1
    monkeypatch.setenv("APP_ENV", "production")
    monkeypatch.setenv("ENGINE_FAIL_OPEN", "1")
    dto = validate(
        {"principal_id": "p", "action_id": "a", "resource_id": "r"}, ErrorSession()
    )
    assert dto["decision"] == "INDETERMINATE"
    # ensure the flag is effectively disabled at runtime
    assert os.getenv("ENGINE_FAIL_OPEN") in (None, "0", "")
