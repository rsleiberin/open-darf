from __future__ import annotations

import json
import os
import tempfile
import threading
import time
import uuid
from typing import Any, Dict, Optional

_lock = threading.Lock()


def _path() -> str:
    """
    Resolve the receipts path on EACH emit so tests/runtime can set RECEIPTS_PATH after import.
    """
    p = os.getenv("RECEIPTS_PATH")
    if not p:
        p = os.path.join(tempfile.gettempdir(), "receipts.jsonl")
    return p


def _enrich(record: Dict[str, Any]) -> Dict[str, Any]:
    out = dict(record)
    if "correlation_id" not in out:
        out["correlation_id"] = str(uuid.uuid4())
    if "ts" not in out:
        out["ts"] = int(time.time() * 1000)
    t0 = out.pop("t0", None)
    if t0 is not None and "latency_ms" not in out:
        try:
            out["latency_ms"] = max(0.0, (time.perf_counter() - float(t0)) * 1000.0)
        except Exception:
            # Don't let observability break writes
            pass
    return out


def emit(payload: Optional[Dict[str, Any]] = None, /, **kwargs: Any) -> str:
    """
    JSONL emitter. Supports BOTH calling styles:
      - emit({"decision": "...", ...})
      - emit(decision="...", reason_code="...", ...)
    Returns the absolute path written to.
    """
    data: Dict[str, Any] = {}
    if payload is not None:
        if not isinstance(payload, dict):
            raise TypeError("payload must be a dict if provided")
        data.update(payload)
    if kwargs:
        data.update(kwargs)

    rec = _enrich(data)
    path = _path()
    os.makedirs(os.path.dirname(path), exist_ok=True)
    line = json.dumps(rec, separators=(",", ":"))
    with _lock:
        with open(path, "a", encoding="utf-8") as f:
            f.write(line + "\n")
    return path
