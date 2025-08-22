from __future__ import annotations
from typing import Iterable, Optional


def count(name: str, value: int = 1, tags: Optional[Iterable[str]] = None) -> None:
    # No-op shim; integrate with statsd/prom later. Must never raise.
    try:
        _ = (name, value, tuple(tags) if tags else ())
    except Exception:
        pass
