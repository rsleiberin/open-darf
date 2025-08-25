from __future__ import annotations
from typing import Any, Mapping
from apps.constitution_engine import engine as _engine


def _obs_emit_decision(decision: str) -> None:
    """
    Observability helper: increments engine decision counters.
    Never throws; safe in prod and tests.
    """
    try:
        from apps import obs as _obs  # lazy import to keep deps light

        d = (decision or "").strip().lower()
        if d:
            _obs.increment(f"engine.decision.{d}", 1.0)
            _obs.increment("engine.decision.total", 1.0)
    except Exception:
        # observability must never throw
        pass


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

    # Observability: emit decision counters (never throws)
    try:
        _obs_emit_decision(decision_str)
    except Exception:
        pass

    return {"decision": decision_str, "reason_code": reason_code}
