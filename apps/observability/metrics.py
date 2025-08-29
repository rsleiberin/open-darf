from __future__ import annotations
import atexit, json, os, time, threading, uuid, pathlib
from typing import Any, Dict
from contextlib import contextmanager

# Feature toggles
_OBS_ON  = os.getenv("OBS_ENABLE", "0") == "1"   # default OFF for CI friendliness
_PERF_ON = os.getenv("RUN_PERF", "0") == "1"

# Metrics directory + session
_METRICS_DIR = pathlib.Path(os.getenv("OBS_METRICS_DIR", "var/metrics"))
_METRICS_DIR.mkdir(parents=True, exist_ok=True)
_SESSION_FILE = _METRICS_DIR / "_session.id"

def _load_or_create_session() -> str:
    sid_env = (os.getenv("OBS_SESSION") or "").strip()
    if sid_env:
        return sid_env
    if _SESSION_FILE.exists():
        s = _SESSION_FILE.read_text(encoding="utf-8").strip()
        if s:
            return s
    s = uuid.uuid4().hex[:8]
    _SESSION_FILE.write_text(s, encoding="utf-8")
    return s

_SESSION = _load_or_create_session()

# State
_lock = threading.Lock()
_counters: Dict[str, Dict[str, int]] = {}
_provider = None

def _file(kind: str) -> pathlib.Path:
    if kind == "snapshot":
        return _METRICS_DIR / f"{_SESSION}_snapshot.jsonl"   # suffix form for tests
    if kind == "timer":
        return _METRICS_DIR / f"timer_{_SESSION}.jsonl"
    return _METRICS_DIR / f"{kind}_{_SESSION}.jsonl"

def _append_jsonl(path: pathlib.Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(payload) + "\n")

# --- Counters (compat shims) ---
def set_provider(provider) -> None:
    global _provider
    _provider = provider  # noqa: PLW0603

def increment(name: str, labels: dict | None = None) -> None:
    labels = dict(labels or {})
    try:
        if _provider and hasattr(_provider, "increment"):
            _provider.increment(name, labels)
        if _OBS_ON:
            with _lock:
                bucket = _counters.setdefault(name, {})
                key = "|".join(f"{k}={labels[k]}" for k in sorted(labels))
                bucket[key] = bucket.get(key, 0) + 1
            _append_jsonl(_file("counter"), {"name": name, "labels": labels, "ts": time.time()})
    except Exception:
        pass

# --- Timers (file-backed for reload safety) ---
def record_time(name: str, seconds: float) -> None:
    if not _PERF_ON:
        return
    try:
        _append_jsonl(_file("timer"), {"name": name, "seconds": float(seconds), "ts": time.time()})
    except Exception:
        pass

@contextmanager
def timer(name: str):
    if not _PERF_ON:
        yield
        return
    t0 = time.perf_counter()
    try:
        yield
    finally:
        record_time(name, time.perf_counter() - t0)

def _reduce_timer_file() -> Dict[str, Dict[str, float]]:
    '''Read timer_<SESSION>.jsonl and return per-name {count,total_seconds,avg_seconds}.'''
    out: Dict[str, Dict[str, float]] = {}
    path = _file("timer")
    if not path.exists():
        return out
    try:
        with path.open("r", encoding="utf-8") as f:
            for line in f:
                try:
                    ev = json.loads(line)
                    n = ev.get("name"); s = float(ev.get("seconds", 0.0))
                    if not n:
                        continue
                    b = out.setdefault(n, {"count": 0.0, "total_seconds": 0.0})
                    b["count"] += 1.0
                    b["total_seconds"] += s
                except Exception:
                    continue
        for n, b in out.items():
            c = max(b.get("count", 0.0), 1.0)
            b["avg_seconds"] = b.get("total_seconds", 0.0) / c
    except Exception:
        return {}
    return out

def write_snapshot() -> None:
    """Write one line to <SESSION>_snapshot.jsonl containing snapshot.avg_seconds.* keys."""
    try:
        timers = _reduce_timer_file() if _PERF_ON else {}
        avg_seconds = {k: v.get("avg_seconds", 0.0) for k, v in timers.items()}
        payload = {
            "generated_at": time.time(),
            "session": _SESSION,
            "snapshot": {
                "avg_seconds": avg_seconds,
                "counters": _counters,
                "source": "obs_v2",
            },
        }
        _append_jsonl(_file("snapshot"), payload)
    except Exception:
        pass

# atexit registration: run when either OBS or PERF is enabled
if _OBS_ON or _PERF_ON:
    try:
        atexit.register(write_snapshot)
    except Exception:
        pass
