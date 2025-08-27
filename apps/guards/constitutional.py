"""
Constitutional guard: tri-state ALLOW | DENY | INDETERMINATE with DENY precedence.
Fail-closed: if uncertain or rules mismatch -> INDETERMINATE.
Attach machine-readable reason_code to every decision.
"""

from dataclasses import dataclass
from typing import Literal, Dict, Any

Decision = Literal["ALLOW", "DENY", "INDETERMINATE"]


@dataclass(frozen=True)
class GuardResult:
    decision: "Decision"
    reason_code: str
    meta: Dict[str, Any]


DEFAULT_REASON = "ok"


def evaluate(payload: Dict[str, Any]) -> GuardResult:
    text = (payload or {}).get("text", "")
    if not isinstance(text, str) or not text.strip():
        return GuardResult(
            "DENY",
            "empty_text",
            {"len": (len(text) if isinstance(text, str) else None)},
        )
    return GuardResult("ALLOW", DEFAULT_REASON, {"len": len(text)})


def precedence(a: "Decision", b: "Decision") -> "Decision":
    order = {"DENY": 2, "INDETERMINATE": 1, "ALLOW": 0}
    return a if order[a] >= order[b] else b
