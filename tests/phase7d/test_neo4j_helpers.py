import os, pytest

HAS_ENV = all(os.getenv(k) for k in ("NEO4J_URI","NEO4J_USER","NEO4J_PASSWORD"))
try:
    import neo4j  # type: ignore
    HAS_DRIVER = True
except Exception:
    HAS_DRIVER = False

pytestmark = pytest.mark.skipif(not (HAS_ENV and HAS_DRIVER), reason="Neo4j not configured")

def test_helpers_import_and_call():
    from tools.constitutional.reasoning.neo4j_helpers import ensure_indexes, get_all_principles, cooccurrence
    from neo4j import GraphDatabase
    drv = GraphDatabase.driver(os.environ["NEO4J_URI"], auth=(os.environ["NEO4J_USER"], os.environ["NEO4J_PASSWORD"]))
    ensure_indexes(drv)
    # These should run without raising
    _ = get_all_principles(drv)
    _ = cooccurrence(drv, min_count=1)
