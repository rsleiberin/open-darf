#!/usr/bin/env bash
set -euo pipefail

SHA1="1111111111111111111111111111111111111111111111111111111111111111"
SHA2="2222222222222222222222222222222222222222222222222222222222222222"

CYPH_CREATE="
CREATE CONSTRAINT IF NOT EXISTS
  FOR (d:TestDoc) REQUIRE d.sha IS UNIQUE;
MERGE (d1:TestDoc {sha: '$SHA1', path:'var/tests/docA.txt'})
MERGE (d2:TestDoc {sha: '$SHA2', path:'var/tests/docB.txt'})
MERGE (d2)-[:DERIVES_FROM]->(d1)
MERGE (d2)-[:HAS_VERSION {n:2}]->(d1);
"

# Write phase (with wrapper)
ops/bin/neo4j_exec.sh "$CYPH_CREATE" >/dev/null

# Read/verify phase (with wrapper)
READQ="MATCH (a:TestDoc {sha:'$SHA1'})<-[:DERIVES_FROM]-(b:TestDoc {sha:'$SHA2'}) RETURN count(b) AS c;"
out="$(ops/bin/neo4j_exec.sh "$READQ" 2>/dev/null || true)"

if echo "$out" | grep -qE '(^|[^0-9])1([^0-9]|$)'; then
  echo "[TEST] neo4j_lineage: PASS"
  # Cleanup
  ops/bin/neo4j_exec.sh "MATCH (n:TestDoc) DETACH DELETE n;" >/dev/null || true
  exit 0
else
  echo "[TEST] neo4j_lineage: FAIL"
  exit 1
fi
