from __future__ import annotations

import json
import os
import tempfile
import threading
import time
import uuid
from typing import Dict, Any

_lock = threading.Lock()


def _path() -> str:
    """
    Resolve path on every call (env-redirect friendly).
    """
    p = os.getenv("RECEIPTS_PATH")
    if not p:
        p = os.path.join(tempfile.gettempdir(), "darf_receipts.jsonl")
    return p


def _enrich(rec: Dict[str, Any]) -> Dict[str, Any]:
    """
    Add correlation_id and timestamp; compute latency if t0 is supplied.
    Never mutates the caller's dict.
    """
    out: Dict[str, Any] = dict(rec)
    # correlation for traceability
    out.setdefault("correlation_id", str(uuid.uuid4()))
    # event time (ms since epoch)
    out.setdefault("ts", int(time.time() * 1000))

    # latency enrichment:
    # - preferred: caller supplies latency_ms
    # - fallback: if caller passes t0 (perf_counter at request start), compute and remove t0
    if "latency_ms" not in out and "t0" in out:
        try:
            start = float(out.get("t0"))  # type: ignore[arg-type]
            out["latency_ms"] = (time.perf_counter() - start) * 1000.0
        except Exception:
            pass
        finally:
            out.pop("t0", None)
    return out


def emit(record: Dict[str, Any]) -> str:
    """
    Append one JSON object per line to the receipts file.
    Thread-safe; resolves path per call; enriches record with correlation & ts.
    Returns the path written to.
    """
    enriched = _enrich(record)

    # Optional metrics wiring (best-effort; no hard dep)
    try:
        from apps.observability import metrics  # type: ignore

        # counters may or may not exist; guard with getattr
        inc = getattr(metrics, "inc", None) or getattr(metrics, "inc_counter", None)
        if callable(inc):
            inc("receipts_emitted", labels={"decision": enriched.get("decision")})
        rec_lat = getattr(metrics, "record_latency_ms", None)
        if callable(rec_lat) and "latency_ms" in enriched:
            rec_lat(decision=enriched.get("decision"), ms=float(enriched["latency_ms"]))
    except Exception:
        # metrics wiring must not throw
        pass

    p = _path()
    line = json.dumps(enriched, separators=(",", ":"), ensure_ascii=False)
    with _lock:
        with open(p, "a", encoding="utf-8") as fh:
            fh.write(line + "\n")
    return p


# Provide a compatibility alias if older code imported a different name
write = emit  # alias
EMIT = emit  # optional constant some code bases prefer
