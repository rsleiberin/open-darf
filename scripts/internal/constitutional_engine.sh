#!/usr/bin/env bash
# Constitutional validation engine for open-darf
set -euo pipefail

# Load environment variables
if [ -f .env ]; then
    set -a
    source .env
    set +a
fi

stamp() { date -u +%Y-%m-%dT%H:%M:%SZ; }
tms() { date +%s%3N; }

# Validation context
CTX_IRREVERSIBLE=${CTX_IRREVERSIBLE:-true}
CTX_HAS_REVIEW=${CTX_HAS_REVIEW:-false}
CTX_ACTOR=${CTX_ACTOR:-"peer_validator"}
CTX_ACTION=${CTX_ACTION:-"validation_run"}

# Generate validation ID
VALIDATION_ID=$(uuidgen 2>/dev/null || cat /proc/sys/kernel/random/uuid 2>/dev/null || echo "$(date +%s)-$$-$RANDOM")
TIMESTAMP=$(stamp)

# Query Neo4j for rule R0
neo_start=$(tms)
RULE_OUTPUT=$(docker compose exec -T neo4j cypher-shell -u neo4j -p "${NEO4J_PASSWORD}" \
  "MATCH (r:Rule {id:'R0'}) RETURN r.requires_review_for_irreversible, r.priority" 2>/dev/null || true)
neo_ms=$(($(tms) - neo_start))

# Parse rule data (skip header, split by comma)
DATA_LINE=$(echo "$RULE_OUTPUT" | awk 'NR==2 {print}')
REQ=$(echo "$DATA_LINE" | awk -F, '{print $1}' | tr -d ' ' | tr '[:upper:]' '[:lower:]')
PRI=$(echo "$DATA_LINE" | awk -F, '{print $2}' | tr -d ' "')

# Apply tri-state logic with DENY precedence
DECISION="INDETERMINATE"
REASON="no_applicable_rule"

if [ "${REQ:-false}" = "true" ] && [ "$CTX_IRREVERSIBLE" = "true" ] && [ "$CTX_HAS_REVIEW" != "true" ]; then
    DECISION="DENY"
    REASON="irreversible_action_without_required_review"
elif [ "$CTX_IRREVERSIBLE" = "false" ]; then
    DECISION="ALLOW"
    REASON="action_is_reversible"
fi

# Store audit receipt in PostgreSQL
postgres_start=$(tms)
DETAILS_JSON="{\"rule_id\":\"R0\",\"reason\":\"$REASON\",\"context\":{\"actor\":\"$CTX_ACTOR\",\"action\":\"$CTX_ACTION\",\"irreversible\":$CTX_IRREVERSIBLE,\"has_review\":$CTX_HAS_REVIEW},\"neo4j_ms\":$neo_ms}"

docker compose exec -T -e PGPASSWORD="${POSTGRES_PASSWORD}" postgres \
  psql -U "${POSTGRES_USER}" -d "${POSTGRES_DB}" -v ON_ERROR_STOP=1 \
  -c "INSERT INTO audit.receipts(component, action, status, details, duration_ms) VALUES ('constitutional_engine', '$CTX_ACTION', '$DECISION', '$DETAILS_JSON'::jsonb, $neo_ms)" \
  >/dev/null 2>&1 || true
postgres_ms=$(($(tms) - postgres_start))
total_ms=$((neo_ms + postgres_ms))

# System fingerprint
OS=$(uname -s)
CPU_CORES=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)
RAM_GB=$(awk '/MemTotal/ {printf "%.1f", $2/1024/1024}' /proc/meminfo 2>/dev/null || echo "unknown")
DOCKER_VERSION=$(docker --version | awk '{print $3}' | tr -d ',' || echo "unknown")

# Output JSON result
cat <<EOF
{
  "receipt_version": "1.0",
  "engine_version": "constitutional-v3",
  "validation_id": "$VALIDATION_ID",
  "timestamp": "$TIMESTAMP",
  "decision": "$DECISION",
  "reason": "$REASON",
  "context": {
    "actor": "$CTX_ACTOR",
    "action": "$CTX_ACTION",
    "irreversible": $CTX_IRREVERSIBLE,
    "has_review": $CTX_HAS_REVIEW
  },
  "performance": {
    "neo4j_query_ms": $neo_ms,
    "postgres_write_ms": $postgres_ms,
    "total_ms": $total_ms
  },
  "system_context": {
    "platform": "$OS",
    "cpu_cores": "$CPU_CORES",
    "ram_gb": "$RAM_GB",
    "docker_version": "$DOCKER_VERSION"
  }
}
EOF
