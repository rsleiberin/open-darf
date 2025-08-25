"""
Precedence adapter: run allow/deny existence query and resolve via decide_precedence.

The adapter is import-safe (lazy driver import) and testable by dependency injection.
"""

from typing import Any, Dict, Optional, Tuple

from .neo4j_allow_deny import build_allow_deny_cypher, parse_allow_deny


def _default_decide_precedence(
    allow_exists: bool, deny_exists: bool
) -> Tuple[str, str]:
    """
    Fallback precedence resolver if engine decide_precedence is not importable.
    DENY > ALLOW; neither -> INDETERMINATE.
    Returns (decision, reason_code).
    """
    if deny_exists:
        return "DENY", "deny_precedence"
    if allow_exists:
        return "ALLOW", "allow_present_no_deny"
    return "INDETERMINATE", "no_allow_no_deny"


def evaluate_precedence_from_graph(
    driver: Any,
    principal_id: str,
    action_id: str,
    resource_id: str,
    *,
    timeout_ms: Optional[int] = None,
    decide_precedence_fn=None,
) -> Dict[str, Any]:
    """
    Execute the bounded allow/deny existence query and resolve a tri-state decision.

    Returns a dict:
      {
        "decision": "ALLOW|DENY|INDETERMINATE",
        "reason_code": str,
        "allow_exists": bool,
        "deny_exists": bool,
        "query_ms": float
      }
    """
    import time

    if decide_precedence_fn is None:
        # Best-effort import from engine; fall back to local
        try:
            # Try common locations
            try:
                from constitution_engine.precedence import decide_precedence as _dp  # type: ignore
            except Exception:
                from engine.precedence import decide_precedence as _dp  # type: ignore
            decide_precedence_fn = _dp
        except Exception:
            decide_precedence_fn = _default_decide_precedence

    cypher = build_allow_deny_cypher()
    params = {
        "principal_id": principal_id,
        "action_id": action_id,
        "resource_id": resource_id,
    }

    t0 = time.perf_counter()

    def _run(tx):
        return list(tx.run(cypher, **params))

    # Lazy import to avoid hard dependency at import time
    try:
        with driver.session() as session:
            records = session.read_transaction(_run)
    except Exception as e:
        # Fail-closed posture defers full engine behavior; here we surface INDETERMINATE
        # with a clear reason for upstream handling.
        return {
            "decision": "INDETERMINATE",
            "reason_code": "graph_query_error",
            "allow_exists": False,
            "deny_exists": False,
            "query_ms": (time.perf_counter() - t0) * 1000.0,
            "error": str(e),
        }

    allow_exists, deny_exists = parse_allow_deny(records)
    decision, reason_code = decide_precedence_fn(allow_exists, deny_exists)
    t_ms = (time.perf_counter() - t0) * 1000.0
    return {
        "decision": decision,
        "reason_code": reason_code,
        "allow_exists": allow_exists,
        "deny_exists": deny_exists,
        "query_ms": t_ms,
    }
