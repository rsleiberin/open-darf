#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OPS="$ROOT/ops/compose"
COMPOSE="$OPS/compose.yml"
ENVF="$OPS/.env"

set -a; . "$ENVF"; set +a

stamp(){ date -u +%Y-%m-%dT%H:%M:%SZ; }

# 1) Quick graph query timings (truthy, not simulated)
neo_time_ms=$(
  /usr/bin/time -f "%e" docker compose --env-file "$OPS/.env" -f "$COMPOSE" exec -T neo4j \
    cypher-shell -a bolt://127.0.0.1:7687 -u neo4j -p "${NEO4J_PASSWORD}" "MATCH (r:Rule) RETURN count(r)" \
    >/dev/null 2>&1 | awk '{print int($1*1000)}'
); rc=$?; [ -z "${neo_time_ms}" ] && neo_time_ms=-1

# 2) Write receipt row (non-interactive)
read -r -d '' SQL <<EOSQL
INSERT INTO audit.receipts(component, action, status, details, duration_ms)
VALUES ('constitutional_engine', 'neo4j_rule_count', '${rc:-1}' = 0 ? 'success' : 'failure',
        jsonb_build_object('query','MATCH (r:Rule) RETURN count(r)'), ${neo_time_ms})
RETURNING id;
EOSQL

docker compose --env-file "$OPS/.env" -f "$COMPOSE" exec -T \
  -e PGPASSWORD="${POSTGRES_PASSWORD}" -e PGCONNECT_TIMEOUT=3 \
  postgres psql -U "${POSTGRES_USER}" -d "${POSTGRES_DB}" -v ON_ERROR_STOP=1 -c "$SQL" >/dev/null || true

echo "OK engine skeleton — neo4j query ${neo_time_ms}ms @ $(stamp)"
