from __future__ import annotations
from typing import Literal, Any

Decision = Literal["ALLOW", "DENY", "INDETERMINATE"]


def _normalize_decision(result: Any) -> Decision:
    # None → DENY
    if result is None:
        return "DENY"
    # String tri-state / booleans as strings
    if isinstance(result, str):
        s = result.strip().upper()
        if s in {"ALLOW", "DENY", "INDETERMINATE"}:
            return s  # type: ignore[return-value]
        if s in {"TRUE", "YES"}:
            return "ALLOW"
        if s in {"FALSE", "NO"}:
            return "DENY"
        return "DENY"
    # Bool
    if isinstance(result, bool):
        return "ALLOW" if result else "DENY"
    # Dict with various common keys
    if isinstance(result, dict):
        for key in ("decision", "result", "state", "status", "allow"):
            if key in result:
                return _normalize_decision(result[key])
        return "DENY"
    # Tuple/list → inspect first
    if isinstance(result, (list, tuple)) and result:
        return _normalize_decision(result[0])
    # Fallback
    return "DENY"


def evaluate_action(action: str, context: dict | None = None) -> Decision:
    """Fail-closed constitutional guard that tolerates multiple return shapes from scope.evaluate()."""
    try:
        from apps.constitution_scope.scope import evaluate as scope_eval  # type: ignore
    except Exception:
        return "DENY"
    try:
        raw = scope_eval(action, context or {})
    except Exception:
        return "DENY"
    decision = _normalize_decision(raw)
    # Deny precedence: only ALLOW passes; INDETERMINATE is treated as DENY by callers.
    return decision
