from __future__ import annotations
import os
import re
from dataclasses import dataclass, asdict
from typing import Any, Dict, Optional
from apps.guards import constitutional as constitutional_guard

_YEAR_RANGE = re.compile(
    r"\b(?:from|between)\s+(\d{4})\s+(?:to|and|-)\s*(\d{4})\b", re.I
)
_SINGLE_YEAR = re.compile(r"\b(?:in|since|on)\s+(\d{4})\b", re.I)


# naive ISO helpers (year-only → Jan 1)
def _iso_year(y: int) -> str:
    return f"{y:04d}-01-01T00:00:00Z"


@dataclass
class TimeSpan:
    start: Optional[str] = None
    end: Optional[str] = None


@dataclass
class TemporalEvent:
    subject: str
    predicate: str
    object: str
    timespan: TimeSpan
    confidence: float
    guard_decision: str
    reason_code: str
    provenance: Dict[str, Any]


def parse_timespan(text: str) -> Optional[TimeSpan]:
    m = _YEAR_RANGE.search(text or "")
    if m:
        y1, y2 = int(m.group(1)), int(m.group(2))
        if y2 < y1:
            y1, y2 = y2, y1
        return TimeSpan(_iso_year(y1), _iso_year(y2))
    m = _SINGLE_YEAR.search(text or "")
    if m:
        y = int(m.group(1))
        return TimeSpan(_iso_year(y), None)
    return None


class TemporalModel:
    """
    Flag-gated temporal inference scaffold:
      - Gate: TEMPORAL_GRAPH_MODEL=1
      - Extracts coarse time spans from text and emits TemporalEvent records.
      - All payloads run through constitutional guard; DENY precedence applied.
    Swap-in for a Graph-State LSTM later while preserving the interface.
    """

    def __init__(self) -> None:
        self.enabled = os.getenv("TEMPORAL_GRAPH_MODEL", "0") == "1"

    def is_enabled(self) -> bool:
        return self.enabled

    def infer(self, text: str) -> Dict[str, Any]:
        pre = constitutional_guard.evaluate({"text": text})
        if pre.decision == "DENY":
            return {
                "decision": "DENY",
                "reason_code": pre.reason_code,
                "events": [],
                "provenance": {"stage": "pre_guard"},
            }
        if not self.enabled:
            return {
                "decision": pre.decision,
                "reason_code": "disabled",
                "events": [],
                "provenance": {"enabled": False, "stage": "disabled_stub"},
            }

        # Extremely simple subject-predicate-object heuristic to pair with timespan
        # Pattern: "<subj> <verb> <obj> [from/in/between ...]"
        tokens = (text or "").strip().split()
        subj = tokens[0] if tokens else ""
        pred = tokens[1] if len(tokens) > 1 else "relates"
        obj = " ".join(tokens[2:]) if len(tokens) > 2 else ""
        ts = parse_timespan(text) or TimeSpan(None, None)

        g_subj = constitutional_guard.evaluate({"text": subj})
        g_obj = constitutional_guard.evaluate({"text": obj})
        final = constitutional_guard.precedence(pre.decision, g_subj.decision)
        final = constitutional_guard.precedence(final, g_obj.decision)

        ev = TemporalEvent(
            subject=subj,
            predicate=pred,
            object=obj,
            timespan=ts,
            confidence=0.6,
            guard_decision=final,
            reason_code="ok",
            provenance={"impl": "TemporalModelStub"},
        )
        return {
            "decision": final,
            "reason_code": "ok",
            "events": [asdict(ev)],
            "provenance": {
                "enabled": True,
                "stage": "inference",
                "impl": "TemporalModel",
            },
        }


def schema_cypher() -> str:
    """
    Offline schema extension proposal (NOT executed here).
    """
    return """
    // Temporal validity properties on relationships
    // (:Entity)-[r:RELATION {valid_from: datetime?, valid_to: datetime?}]->(:Entity)
    // Index suggestions:
    // CREATE INDEX rel_valid_from IF NOT EXISTS FOR ()-[r]-() ON (r.valid_from);
    // CREATE INDEX rel_valid_to   IF NOT EXISTS FOR ()-[r]-() ON (r.valid_to);
    """
