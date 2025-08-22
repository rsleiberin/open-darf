"""
Idempotent Neo4j seeder for local dev.

Usage:
  export NEO4J_URI=bolt://localhost:7687
  export NEO4J_USER=neo4j
  export NEO4J_PASSWORD=please_set_me
  python -m scripts.seed_neo4j
"""

from neo4j import GraphDatabase
import os
import sys

URI = os.getenv("NEO4J_URI", "bolt://localhost:7687")
USER = os.getenv("NEO4J_USER", "neo4j")
PWD = os.getenv("NEO4J_PASSWORD", "please_set_me")

CONSTRAINTS = [
    "CREATE CONSTRAINT principal_id_unique IF NOT EXISTS FOR (p:Principal) REQUIRE p.id IS UNIQUE",
    "CREATE CONSTRAINT action_id_unique IF NOT EXISTS FOR (a:Action) REQUIRE a.id IS UNIQUE",
    "CREATE CONSTRAINT resource_id_unique IF NOT EXISTS FOR (r:Resource) REQUIRE r.id IS UNIQUE",
]

PARAMS = {"pid": "u:demo", "act": "read", "rid": "doc:1"}
SEED = [
    ("MERGE (p:Principal {id:$pid})", {}),
    ("MERGE (a:Action    {id:$act})", {}),
    ("MERGE (r:Resource  {id:$rid})", {}),
    ("MERGE (p)-[:MAY]->(a)-[:ON]->(r)", {}),
]


def main() -> int:
    try:
        driver = GraphDatabase.driver(URI, auth=(USER, PWD))
        with driver.session() as s:
            for stmt in CONSTRAINTS:
                s.run(stmt).consume()
            for stmt, extra in SEED:
                s.run(stmt, **PARAMS, **extra).consume()
            rec = s.run(
                """
                CALL db.labels() YIELD label WITH collect(label) AS L
                CALL db.relationshipTypes() YIELD relationshipType
                WITH L, collect(relationshipType) AS R
                MATCH (p:Principal {id:$pid})-[:MAY]->(a:Action {id:$act})-[:ON]->(r:Resource {id:$rid})
                RETURN L AS labels, R AS rels, p.id AS principal, a.id AS action, r.id AS resource
                """,
                **PARAMS,
            ).single()
        driver.close()
        if rec:
            print("labels:", rec["labels"])
            print("rels  :", rec["rels"])
            print(
                "path  :", rec["principal"], "->", rec["action"], "->", rec["resource"]
            )
        return 0
    except Exception as e:
        print("❌ seed error:", repr(e), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
