from __future__ import annotations
from typing import Any, Mapping
from apps.constitution_engine import engine as _engine


def validate(ctx: Mapping[str, Any], session: Any) -> dict[str, str]:
    """
    Adapter-facing validation: returns a small DTO:
      - decision: "ALLOW" | "DENY" | "INDETERMINATE"
      - reason_code: first reason when indeterminate, else "no-signal"
    """
    # DARF-PHASE2 #242: enforce prod fail-closed (clear ENGINE_FAIL_OPEN)
    import os as _os

    if _os.getenv("APP_ENV", "").lower() in ("production", "prod"):
        _os.environ.pop("ENGINE_FAIL_OPEN", None)
        getattr(_os, "unsetenv", lambda *_: None)("ENGINE_FAIL_OPEN")
    result = _engine.evaluate_request(ctx, session)
    decision_str = str(result.decision)
    reason_code = (
        result.reasons[0]
        if decision_str == "INDETERMINATE" and result.reasons
        else "no-signal"
    )
    return {"decision": decision_str, "reason_code": reason_code}
