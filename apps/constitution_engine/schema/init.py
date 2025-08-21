from __future__ import annotations
import argparse
import sys
from typing import List

SCHEMA_STEPS: List[str] = [
    "CREATE CONSTRAINT IF NOT EXISTS FOR (p:Principal) REQUIRE p.id IS UNIQUE",
    "CREATE CONSTRAINT IF NOT EXISTS FOR (a:Action)    REQUIRE a.id IS UNIQUE",
    "CREATE CONSTRAINT IF NOT EXISTS FOR (r:Resource)  REQUIRE r.id IS UNIQUE",
    "CREATE INDEX IF NOT EXISTS FOR (p:Principal) ON (p.type)",
    "CREATE INDEX IF NOT EXISTS FOR (a:Action)    ON (a.type)",
    "CREATE INDEX IF NOT EXISTS FOR (r:Resource)  ON (r.type)",
]

def run(dry_run: bool = True) -> int:
    if dry_run:
        for stmt in SCHEMA_STEPS:
            print(f"[DRY] {stmt}")
        return 0
    # Lazy import so CI/imports don’t require the neo4j package
    try:
        from neo4j import GraphDatabase  # type: ignore
    except Exception as e:
        print(f"Neo4j driver not available: {e}", file=sys.stderr)
        return 2
    uri = os.getenv("NEO4J_URI", "bolt://localhost:7687")
    user = os.getenv("NEO4J_USER", "neo4j")
    pwd  = os.getenv("NEO4J_PASSWORD", "password")
    driver = GraphDatabase.driver(uri, auth=(user, pwd))
    try:
        with driver.session() as s:
            for stmt in SCHEMA_STEPS:
                s.run(stmt)
                print(f"[APPLY] {stmt}")
    finally:
        driver.close()
    return 0

def main(argv: List[str] | None = None) -> int:
    import os  # placed here to keep top-level minimal deps
    p = argparse.ArgumentParser("constitution schema init")
    p.add_argument("--dry-run", action="store_true", default=False)
    args = p.parse_args(argv)
    return run(dry_run=args.dry_run)

if __name__ == "__main__":
    raise SystemExit(main())
