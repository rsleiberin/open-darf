from __future__ import annotations
from typing import Any, Callable, Dict, Optional, Tuple
from apps.constitution_scope.scope import Decision, evaluate

GuardResult = Tuple[bool, Optional[Any], Dict[str, Any]]


def decide(rule: Any, context: Optional[dict] = None) -> Dict[str, Any]:
    """
    Evaluate a scope rule (callable or literal) into canonical tri-state dict.
    """
    return evaluate(rule, context or {})


def guard_call(
    rule: Any,
    fn: Callable[..., Any],
    *args: Any,
    context: Optional[dict] = None,
    **kwargs: Any,
) -> GuardResult:
    """
    Evaluate 'rule' with optional context; if ALLOW, execute fn(*args, **kwargs).
    Returns (ok: bool, value: Any|None, decision_dict).
    DENY or INDETERMINATE -> ok=False, value=None.
    Never raises; underlying fn exceptions propagate only when ALLOW.
    """
    out = decide(rule, context or {})
    dec = out.get("decision")
    if dec is Decision.ALLOW:
        return True, fn(*args, **kwargs), out
    # DENY or INDETERMINATE -> block
    return False, None, out
