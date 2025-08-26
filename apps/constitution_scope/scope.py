from __future__ import annotations
from enum import Enum
from typing import Any, Callable, Dict, Optional, Tuple, Union


class Decision(str, Enum):
    ALLOW = "ALLOW"
    DENY = "DENY"
    INDETERMINATE = "INDETERMINATE"


ReturnLike = Union[bool, str, Dict[str, Any], Tuple[Any, ...], None]


def _norm_decision(s: str) -> Optional[Decision]:
    s = (s or "").strip().upper()
    if s in ("ALLOW", "ALLOWED", "YES", "TRUE"):
        return Decision.ALLOW
    if s in ("DENY", "DENIED", "NO", "FALSE"):
        return Decision.DENY
    if s in ("INDETERMINATE", "UNKNOWN", "UNSURE", "MAYBE"):
        return Decision.INDETERMINATE
    return None


def coerce_decision(value: ReturnLike) -> Dict[str, Any]:
    """
    Coerce common shapes into a canonical scope decision dict:
      {"decision": Decision, "allow": Optional[bool], "reason": str, "meta": dict}
    Tolerates: bool | str | dict | tuple | None
    Fail-closed to INDETERMINATE.
    """
    try:
        # bool
        if isinstance(value, bool):
            return {
                "decision": Decision.ALLOW if value else Decision.DENY,
                "allow": bool(value),
                "reason": "boolean-return",
                "meta": {},
            }

        # str
        if isinstance(value, str):
            d = _norm_decision(value)
            if d:
                return {
                    "decision": d,
                    "allow": (
                        True
                        if d is Decision.ALLOW
                        else False if d is Decision.DENY else None
                    ),
                    "reason": "string-return",
                    "meta": {"raw": value},
                }
            # unknown string -> indeterminate
            return {
                "decision": Decision.INDETERMINATE,
                "allow": None,
                "reason": "string-unrecognized",
                "meta": {"raw": value},
            }

        # dict
        if isinstance(value, dict):
            meta = dict(value)
            reason = str(
                meta.pop("reason", meta.pop("msg", meta.pop("why", ""))) or ""
            ).strip()
            if "decision" in value:
                d = value["decision"]
                if isinstance(d, Decision):
                    dec = d
                else:
                    dec = _norm_decision(str(d))
                if dec:
                    return {
                        "decision": dec,
                        "allow": (
                            True
                            if dec is Decision.ALLOW
                            else False if dec is Decision.DENY else None
                        ),
                        "reason": reason or "dict-decision",
                        "meta": meta,
                    }
            if "allow" in value:
                allow_flag = bool(value["allow"])
                return {
                    "decision": Decision.ALLOW if allow_flag else Decision.DENY,
                    "allow": allow_flag,
                    "reason": reason or "dict-allow",
                    "meta": meta,
                }
            # fallthrough: dict without decision/allow
            return {
                "decision": Decision.INDETERMINATE,
                "allow": None,
                "reason": reason or "dict-unrecognized",
                "meta": meta,
            }

        # tuple: (decision|bool, [reason])
        if isinstance(value, tuple) and len(value) >= 1:
            head = value[0]
            tail_reason = next((str(x) for x in value[1:] if isinstance(x, str)), "")
            if isinstance(head, bool):
                allow_flag = bool(head)
                return {
                    "decision": Decision.ALLOW if allow_flag else Decision.DENY,
                    "allow": allow_flag,
                    "reason": tail_reason or "tuple-bool",
                    "meta": {"raw": value},
                }
            dec = _norm_decision(str(head))
            if dec:
                return {
                    "decision": dec,
                    "allow": (
                        True
                        if dec is Decision.ALLOW
                        else False if dec is Decision.DENY else None
                    ),
                    "reason": tail_reason or "tuple-decision",
                    "meta": {"raw": value},
                }
            return {
                "decision": Decision.INDETERMINATE,
                "allow": None,
                "reason": "tuple-unrecognized",
                "meta": {"raw": value},
            }

        # None or unsupported -> indeterminate
        return {
            "decision": Decision.INDETERMINATE,
            "allow": None,
            "reason": "none-or-unsupported",
            "meta": {"type": type(value).__name__},
        }
    except Exception as e:  # fail-closed
        return {
            "decision": Decision.INDETERMINATE,
            "allow": None,
            "reason": f"coerce-error:{type(e).__name__}",
            "meta": {},
        }


def evaluate(
    rule: Union[Callable[[Optional[dict]], ReturnLike], ReturnLike],
    context: Optional[dict] = None,
) -> Dict[str, Any]:
    """
    Evaluate a scope rule (callable or literal) into canonical tri-state.
    Always fail-closed; never raises.
    """
    try:
        raw = rule(context) if callable(rule) else rule
    except Exception as e:
        return {
            "decision": Decision.INDETERMINATE,
            "allow": None,
            "reason": f"rule-error:{type(e).__name__}",
            "meta": {},
        }
    return coerce_decision(raw)
