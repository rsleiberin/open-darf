#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OPS="$ROOT/ops/compose"
ENVF="$OPS/.env"
COMPOSE="$OPS/compose.yml"

set -a; . "$ENVF"; set +a

stamp(){ date -u +%Y-%m-%dT%H:%M:%SZ; }
tms(){ date +%s%3N; }

CTX_IRREVERSIBLE=${CTX_IRREVERSIBLE:-true}
CTX_HAS_REVIEW=${CTX_HAS_REVIEW:-false}
CTX_ACTOR=${CTX_ACTOR:-"pipeline"}
CTX_ACTION=${CTX_ACTION:-"write_evidence_bundle"}

# 1) Pull rule from Neo4j (exec inside container; always 127.0.0.1:7687)
t0=$(tms)
ROW=$(docker compose --env-file "$OPS/.env" -f "$COMPOSE" exec -T neo4j \
  cypher-shell -a bolt://127.0.0.1:7687 -u neo4j -p "${NEO4J_PASSWORD}" \
  "MATCH (r:Rule {id:'R0'}) RETURN r.requires_review_for_irreversible AS req, r.priority AS pri" 2>/dev/null \
  | awk 'NR==1{next} {print $1" "$2}')
neo_ms=$(( $(tms) - t0 ))

REQ=$(echo "$ROW" | awk '{print $1}')
PRI_RAW=$(echo "$ROW" | awk '{print $2}')
PRI=$(printf '%s' "$PRI_RAW" | sed 's/^"//; s/"$//')

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

# 3) Build JSON (as a plain shell string; no dollars quoting here)
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

# 4) Send everything to Postgres in ONE psql heredoc:
#    - define the JSON with dollar-quoting inside psql (\set ... $json$...$json$)
#    - use :'DETAILS_JSON'::jsonb in statements (psql expands before SQL parse)
docker compose --env-file "$OPS/.env" -f "$COMPOSE" exec -T \
  -e PGPASSWORD="${POSTGRES_PASSWORD}" -e PGCONNECT_TIMEOUT=3 \
  postgres psql -U "${POSTGRES_USER}" -d "${POSTGRES_DB}" <<'PSQL'
\\set ON_ERROR_STOP on
\\set DECISION '${DECISION}'
\\set NEO_MS ${neo_ms}
\\set DETAILS_JSON \$json$
${DETAILS_JSON}
$json$

-- quick validation
SELECT :'DETAILS_JSON'::jsonb;

DO \$block\$
DECLARE v_id BIGINT;
BEGIN
  INSERT INTO audit.receipts(component, action, status, details, duration_ms)
  VALUES (
    'constitutional_engine',
    'rule_eval_write_evidence_bundle',
    :'DECISION',
    :'DETAILS_JSON'::jsonb,
    :'NEO_MS'
  )
  RETURNING id INTO v_id;
END
\$block\$;
PSQL

echo "DECISION=${DECISION}"
echo "REASON=${REASON}"
echo "TIMINGS neo4j_ms=${neo_ms} @ $(stamp)"
