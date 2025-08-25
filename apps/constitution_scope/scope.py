from __future__ import annotations
from typing import List, Tuple

Tri = str  # "ALLOW" | "DENY" | "INDETERMINATE"


def _split(scope: str) -> List[str]:
    return [p for p in (scope or "").strip().split(":") if p]


def _match_pattern(grant: str, need: str) -> bool:
    """
    grant and need are colon-separated scopes. '*' in grant matches any remaining tail.
    Examples:
      grant='org:*' matches need='org:123' and 'org:123:team:9'
      grant='org:123' matches need='org:123' and 'org:123:project:7'
      grant='doc:write' matches need='doc:write'
    """
    g, n = _split(grant), _split(need)
    if not g or not n:
        return False
    # if grant shorter but exact-prefix allowed (hierarchical)
    for i, part in enumerate(g):
        if part == "*":
            return True
        if i >= len(n):
            # grant longer than need (need can't satisfy)
            return False
        if part != n[i]:
            return False
    # grant consumed; if equal length or grant is strict prefix -> match
    return True


def parse_grants(grants: List[str]) -> Tuple[List[str], List[str]]:
    """
    Separate positive and negative grants:
      - 'doc:write' -> positive
      - '-doc:write' -> negative
    Returns (positives, negatives)
    """
    pos, neg = [], []
    for s in grants or []:
        s = (s or "").strip()
        if not s:
            continue
        if s.startswith("-"):
            neg.append(s[1:])
        else:
            pos.append(s)
    return pos, neg


def evaluate(required: str, grants: List[str]) -> Tri:
    """
    Tri-state evaluator with deny precedence:
      1) If any negative grant matches required -> DENY
      2) Else if any positive grant matches required -> ALLOW
      3) Else -> INDETERMINATE
    """
    pos, neg = parse_grants(grants)
    # Deny precedence
    for g in neg:
        if _match_pattern(g, required):
            return "DENY"
    # Allow if any positive matches
    for g in pos:
        if _match_pattern(g, required):
            return "ALLOW"
    return "INDETERMINATE"
