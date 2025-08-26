"""Non-invasive adapter that lets the guard use registry-defined rules.

- Keeps existing guard code untouched.
- Accepts either a callable or a registry rule name.
- Fail-closed on any error by returning "DENY".
"""

from __future__ import annotations
from typing import Any, Callable

from apps.constitution_scope.registry import get as get_rule

Decision = str  # "ALLOW" | "DENY" | "INDETERMINATE"


def _normalize(rule_or_name: Any) -> Callable[..., Decision] | None:
    if callable(rule_or_name):
        return rule_or_name  # direct callable
    if isinstance(rule_or_name, str):
        try:
            return get_rule(rule_or_name)
        except Exception:
            return None
    return None


def decide_with_rule(rule_or_name: Any, *args, **kwargs) -> Decision:
    try:
        fn = _normalize(rule_or_name)
        if fn is None:
            return "DENY"
        decision = fn(*args, **kwargs)
        return decision if decision in {"ALLOW", "DENY", "INDETERMINATE"} else "DENY"
    except Exception:
        return "DENY"
