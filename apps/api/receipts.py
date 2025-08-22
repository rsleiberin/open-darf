import os
import json
import time
import pathlib
import threading

_LOCK = threading.Lock()


def _path() -> str:
    # Read env every time so tests that setenv AFTER import still work
    return os.getenv("RECEIPTS_PATH", "var/receipts.log")


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
        p = pathlib.Path(_path())
        p.parent.mkdir(parents=True, exist_ok=True)
        with _LOCK, p.open("a", encoding="utf-8") as f:
            f.write(json.dumps(entry, separators=(",", ":")) + "\n")
    except Exception:
        # no-throw observability
        pass
    return entry
