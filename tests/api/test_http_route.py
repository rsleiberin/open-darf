import os
import tempfile
import json
from fastapi.testclient import TestClient
from apps.api import http


def _client(monkeypatch, decision, reason):
    def fake_validate(ctx, session):
        return {"decision": decision, "reason_code": reason}

    monkeypatch.setenv("RECEIPTS_PATH", tempfile.gettempdir() + "/receipts_test.jsonl")
    from apps.api import adapter

    monkeypatch.setattr(adapter, "validate", fake_validate, raising=True)
    monkeypatch.setattr(http, "get_neo4j_session", lambda: object(), raising=True)
    return TestClient(http.app)


def _read_last_line(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            lines = [ln for ln in f.read().splitlines() if ln.strip()]
        return json.loads(lines[-1]) if lines else None
    except FileNotFoundError:
        return None


def test_validate_allow_receipt_and_200(monkeypatch):
    receipts_path = tempfile.gettempdir() + "/receipts_test.jsonl"
    if os.path.exists(receipts_path):
        os.remove(receipts_path)
    c = _client(monkeypatch, "ALLOW", "allow_path:granted")
    res = c.post(
        "/validate", json={"principal_id": "p1", "action_id": "a1", "resource_id": "r1"}
    )
    assert res.status_code == 200
    body = res.json()
    assert body["decision"] == "ALLOW" and body["reason_code"] == "allow_path:granted"
    entry = _read_last_line(receipts_path)
    assert entry and entry["decision"] == "ALLOW" and entry["principal_id"] == "p1"


def test_validate_indeterminate_passthrough(monkeypatch):
    c = _client(monkeypatch, "INDETERMINATE", "neo4j_schema_missing:fail_closed")
    res = c.post(
        "/validate", json={"principal_id": "p3", "action_id": "a3", "resource_id": "r3"}
    )
    assert res.status_code == 200
    assert res.json()["decision"] == "INDETERMINATE"
