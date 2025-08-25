# SPDX-License-Identifier: MIT
# Optional bridge to consult graph precedence when enabled via env.
# Only overrides engine when adapter yields ALLOW or DENY; safe no-op otherwise.

import os
from typing import Tuple, Optional, Any

from constitution_graph.precedence_adapter import evaluate_precedence_from_graph  # type: ignore

_FLAG = {"1", "true", "yes", "on"}


def should_use_graph_precedence() -> bool:
    """Single on/off gate for the precedence adapter."""
    return os.getenv("GRAPH_PRECEDENCE", "").strip().lower() in _FLAG


def resolve_via_graph(
    principal_id: str,
    action_id: str,
    resource_id: str,
    session_or_driver: Any,
) -> Optional[Tuple[str, str]]:
    """
    Returns (decision, reason_code) if graph produced a definitive ALLOW/DENY.
    Returns None on INDETERMINATE or any adapter error to leave engine result unchanged.
    """
    try:
        out = evaluate_precedence_from_graph(
            session_or_driver, principal_id, action_id, resource_id
        )
    except Exception:
        return None

    if not isinstance(out, dict):
        return None
    d = out.get("decision")
    r = out.get("reason_code", "")
    return (d, r) if d in ("ALLOW", "DENY") else None
