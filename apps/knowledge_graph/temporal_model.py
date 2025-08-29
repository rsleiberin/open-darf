from __future__ import annotations
import os
import re
from dataclasses import dataclass
from typing import Any, Dict, List, Optional


def _neutral(reason: str, decision: str = "INDETERMINATE") -> Dict[str, Any]:
    return {
        "summary": "",
        "entities": [],
        "relations": [],
        "temporals": [],
        "events": [],
        "guard_trace": [
            {"component": "temporal_model", "status": "skipped", "reason": reason}
        ],
        "decision": decision,
    }


def _deny(reason: str) -> Dict[str, Any]:
    out = _neutral(reason, decision="DENY")
    out["guard_trace"][0]["status"] = "denied"
    return out


def _norm_year(y: str) -> str:
    y = re.sub(r"[^0-9]", "", y)[:4]
    return f"{int(y):04d}-01-01" if y else ""


@dataclass
class Timespan:
    start: str
    end: str


def _parse_timespan_legacy(text: str) -> Optional[Timespan]:
    """
    Return Timespan(start, end) for coarse year spans like:
      - 'from 2017 to 2019'
      - '2017-2019'
      - single year returns (y, y)
    """
    t = text or ""
    m = re.search(r"\bfrom\s+(\d{4})\s+to\s+(\d{4})\b", t, re.I) or re.search(
        r"\b(\d{4})\s*[-–]\s*(\d{4})\b", t
    )
    if m:
        return Timespan(_norm_year(m.group(1)), _norm_year(m.group(2)))
    m = re.search(r"\b(?:in|since|during)\s+(\d{4})\b", t, re.I) or re.search(
        r"\b(\d{4})\b", t
    )
    if m:
        y = _norm_year(m.group(1))
        return Timespan(y, y)
    return None


def _extract_temporals_from_text(text: str) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    span = parse_timespan(text)
    if span:
        rel = "temporal_span" if span.start != span.end else "temporal_in"
        out.append(
            {
                "subject": None,
                "relation": rel,
                "object": None,
                "time": {"start": span.start, "end": span.end, "granularity": "year"},
                "source": "temporal_regex",
                "confidence": 0.85 if span.start == span.end else 0.9,
            }
        )
    return out


def extract(text: str) -> Dict[str, Any]:
    """
    Temporal model entrypoint (regex shim).
    - DENY on empty/whitespace
    - INDETERMINATE otherwise; 'temporals' populated when patterns match
    """
    if not (text or "").strip():
        return _deny("empty_text")
    temporals = _extract_temporals_from_text(text)
    out = _neutral("parsed")
    out["temporals"] = temporals
    out["guard_trace"][0]["status"] = "ok"
    return out


class TemporalModel:
    """Compatibility wrapper expected by tests."""

    def infer(self, text: str) -> Dict[str, Any]:
        # Respect flag: when off, behave as a neutral stub
        if os.getenv("TEMPORAL_GRAPH_MODEL", "0") != "1":
            out = _neutral("flag_off")
            out["reason_code"] = "disabled"
            return out
        return extract(text)


__all__ = ["TemporalModel", "Timespan", "parse_timespan", "extract"]

# Appended by Phase6B at 20250828-062956


# === Phase6B extension: enhanced temporal parsing (appended) ===
def parse_timespan(text: str):
    """
    Enhanced parser covering:
      - ISO dates: YYYY, YYYY-MM, YYYY-MM-DD
      - Month/Day ranges with year: "March 15–20, 2021" (en dash or hyphen)
      - Open intervals: "since <date>" -> [start, null), "until/thru/to <date>" -> (null, end]
    Returns list[{"start": "...", "end": "...|None", "source":"temporal", "reason_code":"parsed"}].
    If no parse, returns [].
    NOTE: Appended override—keeps disabled path contract elsewhere unchanged.
    """
    import re
    import calendar

    def _last_day(y: int, m: int) -> int:
        return calendar.monthrange(y, m)[1]

    def _norm_iso(y: int, m: int = None, d: int = None):
        if m is None:
            return f"{y:04d}-01-01", f"{y:04d}-12-31"
        if d is None:
            return f"{y:04d}-{m:02d}-01", f"{y:04d}-{m:02d}-{_last_day(y,m):02d}"
        return f"{y:04d}-{m:02d}-{d:02d}", f"{y:04d}-{m:02d}-{d:02d}"

    if not text or not isinstance(text, str):
        return []
    t = text.strip()

    iso_y = re.compile(r"^\s*(?P<y>\d{4})\s*$")
    iso_ym = re.compile(r"^\s*(?P<y>\d{4})-(?P<m>0[1-9]|1[0-2])\s*$")
    iso_ymd = re.compile(
        r"^\s*(?P<y>\d{4})-(?P<m>0[1-9]|1[0-2])-(?P<d>0[1-9]|[12]\d|3[01])\s*$"
    )
    md_range = re.compile(
        r"^\s*(?P<month>[A-Za-z]+)\s+(?P<d1>\d{1,2})\s*[–-]\s*(?P<d2>\d{1,2})\s*,\s*(?P<y>\d{4})\s*$",
        re.X | re.I,
    )
    open_since = re.compile(r"^\s*(since)\s+(?P<date>.+?)\s*$", re.I)
    open_until = re.compile(r"^\s*(until|through|thru|to)\s+(?P<date>.+?)\s*$", re.I)

    # ISO YYYY
    m = iso_y.match(t)
    if m:
        y = int(m.group("y"))
        start, end = _norm_iso(y)
        return [
            {"start": start, "end": end, "source": "temporal", "reason_code": "parsed"}
        ]

    # ISO YYYY-MM
    m = iso_ym.match(t)
    if m:
        y, mo = int(m.group("y")), int(m.group("m"))
        start, end = _norm_iso(y, mo)
        return [
            {"start": start, "end": end, "source": "temporal", "reason_code": "parsed"}
        ]

    # ISO YYYY-MM-DD
    m = iso_ymd.match(t)
    if m:
        y, mo, d = int(m.group("y")), int(m.group("m")), int(m.group("d"))
        start, end = _norm_iso(y, mo, d)
        return [
            {"start": start, "end": end, "source": "temporal", "reason_code": "parsed"}
        ]

    # Month/day range with year
    m = md_range.match(t)
    if m:
        y = int(m.group("y"))
        month_name = m.group("month").lower()
        month_map = {m.lower(): i for i, m in enumerate(calendar.month_name) if m}
        mo = month_map.get(month_name)
        if mo:
            d1, d2 = int(m.group("d1")), int(m.group("d2"))
            d1 = max(1, min(d1, _last_day(y, mo)))
            d2 = max(1, min(d2, _last_day(y, mo)))
            if d2 < d1:
                d1, d2 = d2, d1
            start = f"{y:04d}-{mo:02d}-{d1:02d}"
            end = f"{y:04d}-{mo:02d}-{d2:02d}"
            return [
                {
                    "start": start,
                    "end": end,
                    "source": "temporal",
                    "reason_code": "parsed",
                }
            ]

    # Open intervals (recursive reuse)
    m = open_since.match(t)
    if m:
        inner = m.group("date").strip()
        evs = parse_timespan(inner) or []
        if evs:
            return [
                {
                    "start": evs[0]["start"],
                    "end": None,
                    "source": "temporal",
                    "reason_code": "parsed",
                }
            ]

    m = open_until.match(t)
    if m:
        inner = m.group("date").strip()
        evs = parse_timespan(inner) or []
        if evs:
            return [
                {
                    "start": None,
                    "end": evs[0]["end"],
                    "source": "temporal",
                    "reason_code": "parsed",
                }
            ]

    return []


# === Phase6B observability: temporal ===
try:
    from apps.observability.metrics import start_timer, stop_timer, inc, _OBS_ON
except Exception:
    start_timer = stop_timer = lambda *a, **k: None  # type: ignore
    _OBS_ON = False


def _obs_wrap_temporal_call(fn):
    def _inner(*args, **kwargs):
        t = start_timer("temporal")
        try:
            out = fn(*args, **kwargs)
            return out
        finally:
            stop_timer(t)
            if _OBS_ON:
                inc("temporal", "calls")

    return _inner


if "parse_timespan" in globals():
    parse_timespan = _obs_wrap_temporal_call(parse_timespan)  # type: ignore

# --- Phase6B timing wrapper: temporal ---
try:
    import os
    import time
    from apps.observability import metrics as _obs_m

    _PERF_ON_TM = os.getenv("RUN_PERF", "0") == "1"
    _orig_parse_timespan = parse_timespan  # type: ignore[name-defined]

    def parse_timespan(*a, **kw):  # noqa: F811
        if not _PERF_ON_TM or not hasattr(_obs_m, "record_time"):
            return _orig_parse_timespan(*a, **kw)
        t0 = time.perf_counter()
        try:
            return _orig_parse_timespan(*a, **kw)
        finally:
            _obs_m.record_time("temporal", time.perf_counter() - t0)

except Exception:
    pass
# --- End timing wrapper ---


# --- Phase6B: timer wrapper (idempotent, no extra imports) ---
try:
    from apps.observability import metrics as _obs_metrics
except Exception:  # fallback noop

    class _Noop:
        def __call__(self, *_a, **_k):
            return self

        def __enter__(self):
            return None

        def __exit__(self, exc_type, exc, tb):
            return False

    _obs_metrics = type("M", (), {"timer": lambda *_a, **_k: _Noop()})()

try:
    _parse_timespan_real = parse_timespan

    def parse_timespan_timer_wrapped(text: str):
        with _obs_metrics.timer("temporal"):
            return _parse_timespan_real(text)

    parse_timespan = parse_timespan_timer_wrapped  # override
except Exception:
    pass
