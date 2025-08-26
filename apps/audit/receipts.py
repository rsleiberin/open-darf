from __future__ import annotations
import json
import os
from datetime import datetime, timezone
from typing import Callable, Dict, Any


def _utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def make_jsonl_sink(path: str) -> Callable[[Dict[str, Any]], None]:
    """
    Returns a callable(event_dict) that appends JSONL records to 'path'.
    - Creates parent directory if missing.
    - Adds 'ts' (UTC ISO8601) if not provided.
    - Never raises: swallows I/O errors to avoid breaking core flows.
    """
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)

    def _emit(evt: Dict[str, Any]) -> None:
        try:
            rec = dict(evt)
            rec.setdefault("ts", _utc_iso())
            with open(path, "a", encoding="utf-8") as f:
                f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        except Exception:
            # fail-safe: never raise from audit
            pass

    return _emit
