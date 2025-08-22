from __future__ import annotations

import logging
from typing import Any, Mapping

from apps.constitution_engine.phase2 import ValidationResult, _fail_closed_default
from apps.constitution_engine.precedence import decide_precedence
from apps.observability import metrics

logger = logging.getLogger("constitution_engine")


def _get(ctx: Mapping[str, Any], key: str) -> Any:
    return ctx.get(key)


def evaluate_request(ctx: Mapping[str, Any], neo4j_session) -> ValidationResult:
    """
    Evaluate (principal, action, resource) against the graph and return a ValidationResult.
    Fail-closed on DB/schema errors (devs can opt-in to fail-open via ENGINE_FAIL_OPEN inside _fail_closed_default()).
    """
    try:
        rec = neo4j_session.run(
            """
            MATCH (p:Principal {id: $pid}), (a:Action {id: $aid}), (r:Resource {id: $rid})
            OPTIONAL MATCH (p)-[:ALLOW]->(a)-[:ON]->(r)
            WITH p,a,r, COUNT(*) > 0 AS allow_exists
            OPTIONAL MATCH (p)-[:DENY]->(a)-[:ON]->(r)
            RETURN allow_exists, COUNT(*) > 0 AS deny_exists
            """,
            {
                "pid": str(_get(ctx, "principal_id")),
                "aid": str(_get(ctx, "action_id")),
                "rid": str(_get(ctx, "resource_id")),
            },
        ).single()

        if not rec:
            return _fail_closed_default()

        vr: ValidationResult = decide_precedence(
            bool(rec["allow_exists"]), bool(rec["deny_exists"])
        )

        # Observability (never raise)
        try:
            metrics.count(
                "ce.decision",
                1,
                tags=[f"decision:{getattr(vr.decision, 'value', str(vr.decision))}"],
            )
        except Exception:
            pass
        try:
            logger.info(
                "decision=%s reason=%s",
                getattr(vr.decision, "value", str(vr.decision)),
                getattr(vr, "reason_code", ""),
            )
        except Exception:
            pass

        return vr
    except Exception:
        return _fail_closed_default()


def evaluate_with_driver(ctx: Mapping[str, Any], driver) -> ValidationResult:
    """Helper to evaluate using a neo4j Driver (sync)."""
    try:
        with driver.session() as session:
            return evaluate_request(ctx, session)
    except Exception:
        return _fail_closed_default()


class ConstraintEngine:
    """Back-compat shim to support legacy imports/tests."""

    def __init__(self, neo4j_session):
        self._session = neo4j_session

    def evaluate(self, ctx: Mapping[str, Any]) -> ValidationResult:
        return evaluate_request(ctx, self._session)
