from __future__ import annotations
import os
from typing import Optional, Any, Dict

# Optional import: production path uses real driver; tests inject a stub driver.
try:
    from neo4j import GraphDatabase  # type: ignore
except Exception:  # pragma: no cover
    GraphDatabase = None  # type: ignore

from .prov_logging import IngestionEvent, cypher_for_ingestion


def _get_env(name: str, default: Optional[str] = None) -> Optional[str]:
    return os.getenv(name, default)


def get_driver(
    uri: Optional[str] = None,
    user: Optional[str] = None,
    password: Optional[str] = None,
):
    """
    Construct a Neo4j driver from env or args.
    Raises RuntimeError if driver is unavailable or credentials missing.
    """
    if GraphDatabase is None:
        raise RuntimeError(
            "neo4j driver not installed; install 'neo4j' to use get_driver()"
        )

    uri = uri or _get_env("NEO4J_URI")
    user = user or _get_env("NEO4J_USER")
    password = password or _get_env("NEO4J_PASSWORD")
    if not (uri and user and password):
        raise RuntimeError("NEO4J_URI / NEO4J_USER / NEO4J_PASSWORD must be set")

    return GraphDatabase.driver(uri, auth=(user, password))


def write_ingestion_event(
    ev: IngestionEvent, driver: Optional[Any] = None
) -> Dict[str, Any]:
    """
    Execute Cypher for the ingestion event. Returns a small summary dict.
    Accepts an injected 'driver' to remain unit-testable without real Neo4j.
    """
    cypher = cypher_for_ingestion(ev)
    created_driver = False
    if driver is None:
        driver = get_driver()
        created_driver = True

    try:
        with driver.session() as session:  # type: ignore[attr-defined]
            result = session.run(cypher)  # type: ignore[attr-defined]
            summary: Dict[str, Any] = {"ok": True}
            try:
                consumed = result.consume()  # type: ignore[attr-defined]
                counters = getattr(consumed, "counters", None)
                if counters is not None:
                    summary["counters"] = {
                        "nodes_created": getattr(counters, "nodes_created", 0),
                        "relationships_created": getattr(
                            counters, "relationships_created", 0
                        ),
                        "properties_set": getattr(counters, "properties_set", 0),
                    }
            except Exception:
                pass
    finally:
        if created_driver:
            try:
                driver.close()  # type: ignore[attr-defined]
            except Exception:
                pass

    summary["cypher_len"] = len(cypher)
    return summary
