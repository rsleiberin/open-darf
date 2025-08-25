"""
Optional validation hook to apply precedence + scope checks behind env flags.

Usage (in validation path, near where `decision` and `reason_code` are determined):

    from constitution_engine.validation_hook import apply_optional_hooks
    decision, reason_code = apply_optional_hooks(
        decision, reason_code, principal_id, action_id, resource_id
    )

This is a safe no-op unless env flags are set and providers are available.
"""

import os
from typing import Tuple

# Optional adapters (graceful fallback if missing)
try:
    from constitution_engine.graph_precedence_bridge import (  # type: ignore
        should_use_graph_precedence,
        resolve_via_graph,
    )
except Exception:
    try:
        from engine.graph_precedence_bridge import (  # type: ignore
            should_use_graph_precedence,
            resolve_via_graph,
        )
    except Exception:

        def should_use_graph_precedence():  # type: ignore
            return False

        resolve_via_graph = None  # type: ignore

try:
    from constitution_scope import evaluate_scope  # type: ignore
except Exception:
    evaluate_scope = None  # type: ignore


def _get_driver():
    try:
        from neo4j_provider import get_driver as _get_driver  # type: ignore

        return _get_driver()
    except Exception:
        try:
            from services.neo4j_provider import get_driver as _get_driver  # type: ignore

            return _get_driver()
        except Exception:
            return None


def apply_optional_hooks(
    decision: str,
    reason_code: str,
    principal_id: str,
    action_id: str,
    resource_id: str,
) -> Tuple[str, str]:
    # 1) Optional graph precedence
    try:
        use_graph = should_use_graph_precedence()
    except Exception:
        use_graph = False
    if use_graph and resolve_via_graph is not None:
        drv = _get_driver()
        if drv is not None:
            try:
                d, r, _meta = resolve_via_graph(
                    drv, principal_id, action_id, resource_id
                )
                decision, reason_code = d, r
            except Exception:
                # Keep original decision on adapter errors
                pass

    # 2) Optional scope enforcement (env-gated, minimal viable)
    if os.getenv("CONSTITUTION_ENFORCE_SCOPE", "0") in (
        "1",
        "true",
        "TRUE",
        "yes",
        "on",
    ):
        if evaluate_scope is not None:
            # Minimal adapter: assume required_scope is the action identifier
            out = evaluate_scope(
                principal_scopes=[], required_scope=action_id, resource_scope_hint=None
            )
            if not out.get("authorized", False):
                decision, reason_code = "DENY", "scope_miss"

    return decision, reason_code
