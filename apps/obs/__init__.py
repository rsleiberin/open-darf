from __future__ import annotations
from typing import Dict, List, Any
import os
import time
import json
from pathlib import Path

_counters: Dict[str, float] = {}
_histos: Dict[str, List[float]] = {}
_last_error: str | None = None


def _should_fail() -> bool:
    # Test-only tripwire to simulate sink failures
    return str(os.getenv("OBS_FAIL_ON_EMIT", "")).lower() in {"1", "true", "yes", "on"}


def increment(key: str, value: float = 1.0) -> None:
    global _last_error
    try:
        if _should_fail():
            raise RuntimeError("obs sink fail (increment)")
        _counters[key] = _counters.get(key, 0.0) + float(value)
    except Exception as e:  # never throw
        _last_error = type(e).__name__


def histogram(key: str, value_ms: float) -> None:
    global _last_error
    try:
        if _should_fail():
            raise RuntimeError("obs sink fail (histogram)")
        _histos.setdefault(key, []).append(float(value_ms))
    except Exception as e:
        _last_error = type(e).__name__


def snapshot() -> Dict[str, Any]:
    return {
        "counters": dict(_counters),
        "histograms": {
            k: {
                "n": len(v),
                "p50": _pct(v, 50),
                "p95": _pct(v, 95),
                "max": max(v) if v else 0.0,
            }
            for k, v in _histos.items()
        },
        "last_error": _last_error,
    }


def reset() -> None:
    _counters.clear()
    _histos.clear()
    global _last_error
    _last_error = None


def write_receipt(bucket: str = "obs") -> str:
    """Optional: flush a compact obs snapshot to docs/audit/obs (append-only)."""
    try:
        ts = time.strftime("%Y%m%d-%H%M%S")
        outdir = Path(f"docs/audit/{bucket}") / ts
        outdir.mkdir(parents=True, exist_ok=True)
        path = outdir / "obs.json"
        with open(path, "w", encoding="utf-8") as f:
            json.dump(snapshot(), f, ensure_ascii=False, indent=2)
        return str(path)
    except Exception:
        # never throw
        return ""


def _pct(arr: List[float], p: float) -> float:
    if not arr:
        return 0.0
    s = sorted(float(x) for x in arr)
    k = (len(s) - 1) * (p / 100.0)
    f, c = int(k), min(int(k) + 1, len(s) - 1)
    if f == c:
        return s[int(k)]
    return s[f] + (s[c] - s[f]) * (k - f)
