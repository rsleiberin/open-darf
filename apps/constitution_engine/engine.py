import time
from dataclasses import dataclass
from typing import Any, Dict, List, Optional

try:
    from neo4j import GraphDatabase
except Exception:  # pragma: no cover
    GraphDatabase = None  # type: ignore


@dataclass
class ValidationResult:
    allowed: bool
    reasons: List[str]
    elapsed_ms: float


class ConstraintEngine:
    """
    Phase 1: lightweight constitutional checks with optional Neo4j-backed queries.
    - If NEO4J_* is unset or neo4j driver unavailable, runs in local mode.
    - Interface is stable for upstream integration & benchmarking.
    """

    def __init__(
        self,
        uri: Optional[str] = None,
        user: Optional[str] = None,
        password: Optional[str] = None,
    ):
        self._driver = None
        self._neo = False
        if uri and user and password and GraphDatabase is not None:
            try:
                self._driver = GraphDatabase.driver(
                    uri, auth=(user, password), max_connection_pool_size=4
                )
                # quick ping
                with self._driver.session() as s:
                    s.run("RETURN 1 AS ok").consume()
                self._neo = True
            except Exception:
                # Fallback to local mode if connection fails
                self._driver = None
                self._neo = False

    def close(self) -> None:
        if self._driver is not None:
            self._driver.close()

    # ---- public API ----
    def validate(self, op: Dict[str, Any]) -> ValidationResult:
        """
        Validate a requested operation against constitutional constraints.
        Expected op keys (extensible): principal, action, resource, node
        """
        t0 = time.perf_counter()
        reasons: List[str] = []

        # Basic schema checks (fast)
        missing = [k for k in ("principal", "action", "resource") if k not in op]
        if missing:
            reasons.append(f"missing: {','.join(missing)}")
            return ValidationResult(allowed=False, reasons=reasons, elapsed_ms=_ms(t0))

        # Local fast checks (placeholder for concrete rules)
        if op.get("action") in {"delete_system", "grant_root"}:
            reasons.append("action denied by baseline constitution")
            return ValidationResult(allowed=False, reasons=reasons, elapsed_ms=_ms(t0))

        # Optional Neo4j policy lookups
        if self._neo:
            try:
                with self._driver.session() as s:
                    # Simple pattern: require an ALLOW edge Principal-[:MAY]->(Action)-[:ON]->(Resource)
                    q = """
                    MATCH (p:Principal {id:$pid})-[:MAY]->(a:Action {id:$act})-[:ON]->(r:Resource {id:$rid})
                    RETURN 1 AS ok
                    """
                    rec = s.run(
                        q,
                        pid=str(op["principal"]),
                        act=str(op["action"]),
                        rid=str(op["resource"]),
                    ).single()
                    if not rec:
                        reasons.append("no explicit ALLOW path in graph")
                        return ValidationResult(
                            allowed=False, reasons=reasons, elapsed_ms=_ms(t0)
                        )
            except Exception as e:  # degrade gracefully
                reasons.append(f"neo4j_error:{type(e).__name__}")
                # allow local decision to proceed even if graph lookup is flaky

        # Passed all checks here
        return ValidationResult(allowed=True, reasons=reasons, elapsed_ms=_ms(t0))


def _ms(t0: float) -> float:
    return (time.perf_counter() - t0) * 1000.0
