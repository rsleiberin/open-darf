#!/usr/bin/env python3
from __future__ import annotations
from enum import Enum
from typing import Iterable, Optional, Tuple, Dict, Any

class Decision(str, Enum):
    ALLOW = "ALLOW"
    DENY = "DENY"
    INDETERMINATE = "INDETERMINATE"

def combine_decisions(decisions: Iterable[Decision]) -> Decision:
    """Deny precedence: if any DENY -> DENY; elif all ALLOW -> ALLOW; else INDETERMINATE."""
    has_deny = False
    has_indet = False
    has_allow = False
    for d in decisions:
        if d == Decision.DENY:
            has_deny = True
        elif d == Decision.ALLOW:
            has_allow = True
        else:
            has_indet = True
    if has_deny:
        return Decision.DENY
    if has_allow and not has_indet:
        return Decision.ALLOW
    return Decision.INDETERMINATE

def fail_closed(*signals: Optional[bool]) -> Decision:
    """Return INDETERMINATE if any signal is None/unknown; ALLOW if all True; DENY if any False."""
    saw_none = any(s is None for s in signals)
    saw_false = any(s is False for s in signals)
    if saw_false:
        return Decision.DENY
    if saw_none:
        return Decision.INDETERMINATE
    return Decision.ALLOW

def decide_with_constraints(scores: Dict[str,float], constraints: Dict[str,bool|None]) -> Tuple[Decision, Dict[str,Any]]:
    """
    Example policy:
      - hard_filters: any False -> DENY
      - unknowns -> INDETERMINATE (fail-closed)
      - if all True -> ALLOW
    """
    hard_results = []
    rationale = {}
    for key, val in constraints.items():
        rationale[key] = val
        if val is False:
            hard_results.append(Decision.DENY)
        elif val is True:
            hard_results.append(Decision.ALLOW)
        else:
            hard_results.append(Decision.INDETERMINATE)
    overall = combine_decisions(hard_results)
    return overall, {"scores": scores, "constraints": rationale, "decision": overall.value}
