import json
import os
import time

from apps.api import receipts


def _read_last_line(path: str):
    with open(path, "rb") as f:
        data = f.read().splitlines()
        assert data, "expected at least one receipt line"
        return json.loads(data[-1].decode("utf-8"))


def test_emit_enriches_with_correlation_ts_and_latency_from_t0(tmp_path):
    # route-like payload with t0 (perf counter)
    os.environ["RECEIPTS_PATH"] = str(tmp_path / "r1.jsonl")
    t0 = time.perf_counter()
    p = receipts.emit(
        {"decision": "ALLOW", "reason_code": "TEST_OK", "principal_id": "p1", "t0": t0}
    )
    rec = _read_last_line(p)
    assert rec["decision"] == "ALLOW"
    assert rec["reason_code"] == "TEST_OK"
    assert rec["principal_id"] == "p1"
    # enrichment fields present
    assert (
        "correlation_id" in rec
        and isinstance(rec["correlation_id"], str)
        and len(rec["correlation_id"]) >= 8
    )
    assert "ts" in rec and isinstance(rec["ts"], int)
    assert "latency_ms" in rec and rec["latency_ms"] >= 0.0
    # internal t0 must not leak
    assert "t0" not in rec


def test_emit_reads_env_per_call_and_redirects_safely(tmp_path):
    # first write
    p1 = tmp_path / "a.jsonl"
    os.environ["RECEIPTS_PATH"] = str(p1)
    receipts.emit({"decision": "DENY", "reason_code": "X", "principal_id": "p2"})
    assert p1.exists()

    # change env and write again — should go to a different file
    p2 = tmp_path / "b.jsonl"
    os.environ["RECEIPTS_PATH"] = str(p2)
    receipts.emit({"decision": "ALLOW", "reason_code": "Y", "principal_id": "p3"})
    assert p2.exists()
    assert p1.read_text() != "" and p2.read_text() != ""
