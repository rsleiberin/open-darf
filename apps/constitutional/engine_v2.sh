#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OPS="$ROOT/ops/compose"
COMPOSE="$OPS/compose.yml"
ENVF="$OPS/.env"

set -a; . "$ENVF"; set +a

stamp(){ date -u +%Y-%m-%dT%H:%M:%SZ; }
tms(){ date +%s%3N; }   # ms since epoch

# Context (real values; can be overridden via env)
CTX_IRREVERSIBLE=${CTX_IRREVERSIBLE:-true}
CTX_HAS_REVIEW=${CTX_HAS_REVIEW:-false}
CTX_ACTOR=${CTX_ACTOR:-"pipeline"}
CTX_ACTION=${CTX_ACTION:-"write_evidence_bundle"}

# 1) Pull rule flags from Neo4j (plain output; robust parsing)
t0=$(tms)
FLAGS=$(docker compose --env-file "$OPS/.env" -f "$COMPOSE" exec -T neo4j \
  cypher-shell -a bolt://127.0.0.1:7687 -u neo4j -p "${NEO4J_PASSWORD}" \
  "MATCH (r:Rule {id:'R0'}) RETURN r.requires_review_for_irreversible AS req, r.priority AS pri" 2>/dev/null \
  | awk 'NR==1{next} {print $1" "$2}')
neo_ms=$(( $(tms) - t0 ))

REQ=$(echo "$FLAGS" | awk '{print $1}')
PRI=$(echo "$FLAGS" | awk '{print $2}')

# 2) Tri-state with DENY precedence
DECISION="INDETERMINATE"
REASON="no_applicable_rule"
if [ "${REQ:-false}" = "true" ] && [ "${CTX_IRREVERSIBLE}" = "true" ] && [ "${CTX_HAS_REVIEW}" != "true" ]; then
  DECISION="DENY"
  REASON="irreversible_without_review (R0)"
elif [ "${CTX_IRREVERSIBLE}" = "false" ]; then
  DECISION="ALLOW"
  REASON="non_irreversible"
fi

# 3) Build JSON as a single-quoted SQL dollar-quoted literal to avoid shell escaping issues
DETAILS_JSON=$(cat <<EOF
{
  "context": {
    "actor": "${CTX_ACTOR}",
    "action": "${CTX_ACTION}",
    "irreversible": ${CTX_IRREVERSIBLE},
    "has_review": ${CTX_HAS_REVIEW}
  },
  "neo4j_ms": ${neo_ms},
  "rule_priority": "${PRI:-unknown}",
  "rule_id": "R0"
}
EOF
)

# 4) Insert receipt (no JSON parsing by psql; we use $$…$$ dollar-quoting)
SQL=$(cat <<'EOSQL'
DO $$
DECLARE v_id BIGINT;
BEGIN
  INSERT INTO audit.receipts(component, action, status, details, duration_ms)
  VALUES ('constitutional_engine', 'rule_eval_write_evidence_bundle', %STATUS%, %DETAILS%::jsonb, %NEO_MS%)
  RETURNING id INTO v_id;
END $$;
EOSQL
)

SQL=${SQL//%STATUS%/"'$DECISION'"}
# Escape $$ inside JSON if ever present (unlikely here), then wrap with $$…$$
SAFE_DETAILS=$(printf '%s' "$DETAILS_JSON" | sed 's/\$\$/\\$\\$/g')
SQL=${SQL//%DETAILS%/$$$SAFE_DETAILS$$}
SQL=${SQL//%NEO_MS%/$neo_ms}

# Execute insert (bounded by PGCONNECT_TIMEOUT via environment)
docker compose --env-file "$OPS/.env" -f "$COMPOSE" exec -T \
  -e PGPASSWORD="${POSTGRES_PASSWORD}" -e PGCONNECT_TIMEOUT=3 \
  postgres psql -U "${POSTGRES_USER}" -d "${POSTGRES_DB}" -v ON_ERROR_STOP=1 -c "$SQL" >/dev/null

echo "DECISION=${DECISION}"
echo "REASON=${REASON}"
echo "TIMINGS neo4j_ms=${neo_ms} @ $(stamp)"
