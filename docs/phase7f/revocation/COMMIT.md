# Phase 7F — Revocation Commit Executor (guarded)

Reads a `revocation_plan.json` and performs guarded deletions.

## Dry-run (default)
APPLY=0 (default) writes receipts only; no external mutations.

## Apply (idempotent, guarded)
Requires cypher-shell and env:
- NEO4J_URI, NEO4J_USER, NEO4J_PASS
Optional Qdrant:
- QDRANT_URL, QDRANT_COLLECTION (default: documents)

Example:
APPLY=1 NEO4J_URI=bolt://localhost:7687 NEO4J_USER=neo4j NEO4J_PASS=*** \\
  scripts/phase7f/revocation_commit.py --plan var/receipts/phase7f/revocation_demo/<ts>/revocation_plan.json
