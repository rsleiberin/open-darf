from typing import Iterable, Optional


def _match_scope(principal_scope: str, required: str) -> bool:
    """Segment-wise wildcard match, using ':' as a separator."""
    ps = principal_scope.split(":")
    rs = required.split(":")
    # allow ps to be shorter; '*' matches any remainder
    for i, seg in enumerate(ps):
        if seg == "*":
            return True
        if i >= len(rs) or seg != rs[i]:
            return False
    return len(ps) == len(rs)


def evaluate_scope(
    principal_scopes: Iterable[str],
    required_scope: str,
    resource_scope_hint: Optional[str] = None,
):
    """
    Returns dict: {authorized, matched_scope, reason_code}
    If resource_scope_hint is provided, required is augmented as f"{required_scope}:{resource_scope_hint}".
    """
    if resource_scope_hint:
        required = f"{required_scope}:{resource_scope_hint}"
    else:
        required = required_scope

    for s in principal_scopes or []:
        if _match_scope(s, required):
            return {
                "authorized": True,
                "matched_scope": s,
                "reason_code": "scope_match",
            }
    return {"authorized": False, "matched_scope": None, "reason_code": "scope_miss"}
