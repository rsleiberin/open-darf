from __future__ import annotations
from typing import Any, Literal, TypedDict


class ValidationDTO(TypedDict):
    decision: Literal["ALLOW", "DENY", "INDETERMINATE"]
    reason_code: str


def to_validation_dto(vr: Any) -> ValidationDTO:
    # vr is expected to have attributes: decision (Enum with .value) and reason_code (str)
    decision = getattr(vr, "decision", None)
    decision_value = getattr(decision, "value", str(decision))
    return {"decision": decision_value, "reason_code": getattr(vr, "reason_code", "")}
