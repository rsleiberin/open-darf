#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OPS="$ROOT/ops/compose"
COMPOSE="$OPS/compose.yml"
ENVF="$OPS/.env"

set -a; . "$ENVF"; set +a

stamp(){ date -u +%Y-%m-%dT%H:%M:%SZ; }
tstart(){ date +%s%3N; }  # ms
tend_ms(){ echo $(( $(date +%s%3N) - $1 )); }

# Input context (could be piped JSON later). For now, a concrete scenario:
# irreversible=true, has_prior_review=false -> should trigger DENY via R0.
ctx_irreversible=${CTX_IRREVERSIBLE:-true}
ctx_has_review=${CTX_HAS_REVIEW:-false}
ctx_actor=${CTX_ACTOR:-"pipeline"}
ctx_action=${CTX_ACTION:-"write_evidence_bundle"}

# Pull flags from Neo4j (real query)
neo_ms_start=$(tstart)
flags=$(docker compose --env-file "$OPS/.env" -f "$COMPOSE" exec -T neo4j \
  cypher-shell -a bolt://127.0.0.1:7687 -u neo4j -p "${NEO4J_PASSWORD}" \
  "MATCH (r:Rule {id:'R0'}) RETURN r.requires_review_for_irreversible AS req, r.priority AS pri" \
  | awk 'NR==1{next} {print $1,$2}' )
neo_ms=$(tend_ms "$neo_ms_start")

req=$(echo "$flags" | awk '{print $1}')
pri=$(echo "$flags" | awk '{print $2}')

decision="INDETERMINATE"
reason="no_applicable_rule"
if [ "${req:-false}" = "true" ] && [ "${ctx_irreversible}" = "true" ] && [ "${ctx_has_review}" != "true" ]; then
  # DENY precedence honored per architect guidance
  decision="DENY"
  reason="irreversible_without_review (R0)"
elif [ "${ctx_irreversible}" = "false" ]; then
  decision="ALLOW"
  reason="non_irreversible"
fi

# Write receipt to Postgres (real row, JSON details)
details=$(cat <<EOS
{
  "context":{"actor":"${ctx_actor}","action":"${ctx_action}","irreversible":${ctx_irreversible},"has_review":${ctx_has_review}},
  "neo4j_ms": ${neo_ms},
  "rule_priority":"${pri:-unknown}",
  "rule_id":"R0"
}
EOS
)
psql_ms_start=$(tstart)
docker compose --env-file "$OPS/.env" -f "$COMPOSE" exec -T \
  -e PGPASSWORD="${POSTGRES_PASSWORD}" postgres psql -U "${POSTGRES_USER}" -d "${POSTGRES_DB}" \
  -v ON_ERROR_STOP=1 -c "INSERT INTO audit.receipts(component,action,status,details,duration_ms)
  VALUES ('constitutional_engine','rule_eval_${ctx_action}','${decision}','${details//\'/\'\'}', ${neo_ms})" >/dev/null || true
psql_ms=$(tend_ms "$psql_ms_start")

echo "DECISION=${decision}"
echo "REASON=${reason}"
echo "TIMINGS neo4j_ms=${neo_ms} psql_ms=${psql_ms} @ $(stamp)"
