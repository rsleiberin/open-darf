from __future__ import annotations
from enum import Enum
from typing import Any, Dict, List, Tuple, Optional


# JSON-safe enum: behaves like str for serialization; identity-safe for tests
class Decision(str, Enum):
    ALLOW = "ALLOW"
    DENY = "DENY"
    INDETERMINATE = "INDETERMINATE"


def _allow_flag(dec: Decision) -> Optional[bool]:
    return True if dec is Decision.ALLOW else False if dec is Decision.DENY else None


def _to_dec(
    dec: Decision, reason: Optional[str] = None, meta: Optional[Dict[str, Any]] = None
) -> Dict[str, Any]:
    out: Dict[str, Any] = {"decision": dec, "allow": _allow_flag(dec)}
    if reason is not None:
        out["reason"] = reason
    if meta is not None:
        out["meta"] = meta
    return out


# ---------- ACL helpers (resource, grants) ----------


def _match(pattern: str, resource: str) -> bool:
    if pattern == "*" or pattern == "":
        return True
    if pattern.endswith(":*"):
        p = pattern[:-2]
        return resource == p or resource.startswith(p + ":")
    # Non-wildcard: hierarchical prefix match
    return resource == pattern or resource.startswith(pattern + ":")


def parse_grants(grants: List[str]) -> Tuple[List[str], List[str]]:
    pos, neg = [], []
    if not isinstance(grants, (list, tuple)):
        return pos, neg
    for g in grants:
        if not isinstance(g, str) or not g:
            continue
        if g.startswith("-"):
            neg.append(g[1:])
        else:
            pos.append(g)
    return pos, neg


def _evaluate_acl(resource: str, grants: List[str]) -> str:
    pos, neg = parse_grants(grants)
    if any(_match(n, resource) for n in neg):
        return "DENY"
    if any(_match(p, resource) for p in pos):
        return "ALLOW"
    return "INDETERMINATE"


# ---------- Literal/rule evaluation ----------

_SYNONYMS_ALLOW = {"ALLOW", "ALLOWED", "YES", "TRUE", "OK", "PERMIT", "PERMITTED"}
_SYNONYMS_DENY = {"DENY", "DENIED", "NO", "FALSE", "BLOCK", "BLOCKED"}


def coerce_decision(value: Any) -> Dict[str, Any]:
    # Bool
    if value is True:
        return _to_dec(Decision.ALLOW, reason="bool-true")
    if value is False:
        return _to_dec(Decision.DENY, reason="bool-false")

    # Enum passthrough
    if isinstance(value, Decision):
        return _to_dec(value)

    # String literals (with synonyms)
    if isinstance(value, str):
        v = value.strip().upper()
        if v in _SYNONYMS_ALLOW:
            return _to_dec(Decision.ALLOW, reason="literal-allow")
        if v in _SYNONYMS_DENY:
            return _to_dec(Decision.DENY, reason="literal-deny")
        if v == "INDETERMINATE":
            return _to_dec(Decision.INDETERMINATE, reason="literal-indeterminate")
        return _to_dec(Decision.INDETERMINATE, reason="literal-unknown")

    # Dict with {decision: ...} and/or {allow: bool}
    if isinstance(value, dict):
        if "allow" in value:
            return _to_dec(
                Decision.ALLOW if bool(value["allow"]) else Decision.DENY,
                reason=value.get("reason"),
            )
        if "decision" in value:
            inner = coerce_decision(value["decision"])
            return _to_dec(
                inner["decision"],
                reason=value.get("reason", inner.get("reason")),
                meta=value.get("meta") or value.get("context"),
            )
        return _to_dec(Decision.INDETERMINATE, reason="dict-no-decision")

    # Tuple: (thing, reason?) → use reason if provided
    if isinstance(value, tuple) and value:
        base = coerce_decision(value[0])
        reason = base.get("reason")
        if len(value) >= 2 and isinstance(value[1], str):
            reason = value[1]
        return _to_dec(base["decision"], reason=reason)

    # Callable rules handled by decide()
    return _to_dec(Decision.INDETERMINATE, reason="coerce-unknown")


def decide(rule_or_value: Any, context: Optional[dict] = None) -> Dict[str, Any]:
    if callable(rule_or_value):
        try:
            out = rule_or_value(context or {})
        except Exception as exc:  # fail-closed but auditable
            return _to_dec(Decision.INDETERMINATE, reason=f"rule-error:{exc}")
        return coerce_decision(out)
    return coerce_decision(rule_or_value)


# ---------- Polymorphic evaluate() ----------
# Modes:
# 1) evaluate(resource, grants) -> "ALLOW|DENY|INDETERMINATE" (string, ACL mode)
# 2) evaluate(rule_or_value, context=None) -> {"decision": Decision.*, "allow": ..., ...}


def evaluate(arg1: Any, arg2: Optional[Any] = None):
    if isinstance(arg2, (list, tuple)) and isinstance(arg1, str):
        return _evaluate_acl(arg1, list(arg2))
    return decide(arg1, context=arg2 if isinstance(arg2, dict) else None)


__all__ = ["Decision", "parse_grants", "evaluate", "decide", "coerce_decision"]
