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


def parse_timespan(text: str) -> Optional[Timespan]:
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
