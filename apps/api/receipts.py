import os
import json
import time
import pathlib
import threading

_PATH = os.getenv("RECEIPTS_PATH", "var/receipts.log")
_LOCK = threading.Lock()


def emit(
    *,
    decision: str,
    reason_code: str,
    principal_id: str,
    action_id: str,
    resource_id: str,
    extra=None
):
    entry = {
        "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "decision": decision,
        "reason_code": reason_code,
        "principal_id": principal_id,
        "action_id": action_id,
        "resource_id": resource_id,
        "extra": extra or {},
    }
    try:
        p = pathlib.Path(_PATH)
        p.parent.mkdir(parents=True, exist_ok=True)
        with _LOCK, p.open("a", encoding="utf-8") as f:
            f.write(json.dumps(entry, separators=(",", ":")) + "\n")
    except Exception:
        pass
    return entry
