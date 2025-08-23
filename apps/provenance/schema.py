from __future__ import annotations
from typing import Any, Dict, List


def constraint_statements() -> List[str]:
    """
    Idempotent schema statements for PROV-O flavored nodes.
    Uses IF NOT EXISTS so it's safe to run repeatedly.
    """
    return [
        # Uniqueness
        "CREATE CONSTRAINT doc_id_unique IF NOT EXISTS FOR (d:Entity:Document) REQUIRE d.id IS UNIQUE",
        "CREATE CONSTRAINT act_id_unique IF NOT EXISTS FOR (a:Activity) REQUIRE a.id IS UNIQUE",
        "CREATE CONSTRAINT agent_id_unique IF NOT EXISTS FOR (g:Agent) REQUIRE g.id IS UNIQUE",
        # Helpful property indexes for hot paths
        "CREATE INDEX doc_type_idx IF NOT EXISTS FOR (d:Entity:Document) ON (d.type)",
        "CREATE INDEX act_type_idx IF NOT EXISTS FOR (a:Activity) ON (a.type)",
        "CREATE INDEX agent_type_idx IF NOT EXISTS FOR (g:Agent) ON (g.type)",
    ]


def apply_constraints(driver: Any) -> Dict[str, Any]:
    """
    Apply constraints/indexes using an injected Neo4j driver.
    Returns a summary with counts and the statements executed.
    """
    stmts = constraint_statements()
    executed = 0
    created_constraints = 0
    created_indexes = 0

    with driver.session() as session:  # type: ignore[attr-defined]
        for cypher in stmts:
            res = session.run(cypher)  # type: ignore[attr-defined]
            executed += 1
            try:
                c = res.consume().counters  # type: ignore[attr-defined]
                # counters fields presence may vary by driver version; guard with getattr
                created_constraints += getattr(c, "constraints_added", 0)
                created_indexes += getattr(c, "indexes_added", 0)
            except Exception:
                pass

    return {
        "ok": True,
        "executed": executed,
        "created_constraints": created_constraints,
        "created_indexes": created_indexes,
        "statements": stmts,
    }
