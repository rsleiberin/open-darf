#!/usr/bin/env bash
set -euo pipefail
query="${1:-}"
if [[ -z "$query" ]]; then
  cat >&2 <<USAGE
usage: neo4j_exec.sh "<CYPHER>" 
  Runs cypher inside darf-neo4j-1 via cypher-shell with best-effort auth.
USAGE
  exit 2
fi

NEO_CONTAINER="darf-neo4j-1"
AUTH="$(docker inspect -f '{{range .Config.Env}}{{println .}}{{end}}' "$NEO_CONTAINER" 2>/dev/null | awk -F= '/^NEO4J_AUTH=/{print $2}')"
ADDR="bolt://localhost:7687"

try() { docker exec -i "$NEO_CONTAINER" cypher-shell "$@" "$query" >/dev/null 2>&1; }

# 1) Use explicit creds if provided (neo4j/<pass> or user/pass)
if [[ -n "$AUTH" && "$AUTH" != "none" ]]; then
  USER="${AUTH%/*}"; PASS="${AUTH#*/}"
  try -a "$ADDR" -u "$USER" -p "$PASS" && exec docker exec -i "$NEO_CONTAINER" cypher-shell -a "$ADDR" -u "$USER" -p "$PASS" "$query"
fi

# 2) Try default neo4j/neo4j (common dev default)
try -a "$ADDR" -u neo4j -p neo4j && exec docker exec -i "$NEO_CONTAINER" cypher-shell -a "$ADDR" -u neo4j -p neo4j "$query"

# 3) Try no auth (NEO4J_AUTH=none)
if docker exec -i "$NEO_CONTAINER" cypher-shell -a "$ADDR" "RETURN 1;" >/dev/null 2>&1; then
  exec docker exec -i "$NEO_CONTAINER" cypher-shell -a "$ADDR" "$query"
fi

echo "[neo4j_exec] ERROR: Unable to authenticate to cypher-shell" >&2
exit 1
