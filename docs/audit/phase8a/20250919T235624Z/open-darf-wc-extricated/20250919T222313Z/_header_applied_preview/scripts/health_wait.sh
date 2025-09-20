# DO NOT COMMIT THIS FILE — PREVIEW OF PROPOSED HEADER
# Header: Purpose
# One or two plain sentences describing what this file does and who runs it.

# Header: Inputs
# - Environment variables / CLI flags
# - External services called (if any)

# Header: Outputs
# - Files/receipts generated
# - Network side effects (ports/endpoints touched)

# Header: Data Flow
# Source → Transform/Validation → Sink (mention receipts directory)

# Header: Failure Modes & Recovery
# Common errors, detection cues, and operator actions.

# Header: Idempotence & Teardown
# What is safe to re-run; cleanup behavior.

# Header: Security & Privacy Notes
# Sensitive ops (if any). Stays local unless explicit user consent for publishing evidence.

#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source "./scripts/_hb.sh"

echo "===\n===\n==="
echo "=== Open-DARF · Health wait with heartbeat ==="

if docker compose version >/dev/null 2>&1; then DC="docker compose"; else DC="docker-compose"; fi
$DC up -d minio qdrant neo4j postgres

echo "[1] Qdrant readiness (up to 90s)…"
hb_start "Qdrant healthz"
ok_q="fail"
for i in {1..45}; do curl -fsS http://localhost:6333/healthz >/dev/null && { ok_q="ok"; break; } || sleep 2; done || true
hb_stop

echo "[2] Neo4j readiness via cypher-shell (up to 120s)…"
hb_start "Neo4j cypher-shell RETURN 1"
ok_n="fail"
for i in {1..60}; do docker exec darf-neo4j cypher-shell -u neo4j -p darf_graph_password 'RETURN 1;' >/dev/null 2>&1 && { ok_n="ok"; break; } || sleep 2; done || true
hb_stop

echo "[3] MinIO/Postgres quick probes…"
hb_start "MinIO /health/live"
ok_m="fail"
for i in {1..30}; do curl -fsS http://localhost:9000/minio/health/live >/dev/null && { ok_m="ok"; break; } || sleep 2; done || true
hb_stop

hb_start "Postgres pg_isready"
ok_p="fail"
for i in {1..30}; do docker exec darf-postgres pg_isready -U darf_user -d darf_audit >/dev/null 2>&1 && { ok_p="ok"; break; } || sleep 2; done || true
hb_stop

echo "=== Health Summary ==="
printf "MinIO   : %s\n" "$ok_m"
printf "Qdrant  : %s\n" "$ok_q"
printf "Neo4j   : %s\n" "$ok_n"
printf "Postgres: %s\n" "$ok_p"

mkdir -p results
jq -n --arg ts "$(date -Is)" \
      --arg minio "$ok_m" --arg qdrant "$ok_q" \
      --arg neo4j "$ok_n" --arg postgres "$ok_p" \
      '{ts:$ts, minio:$minio, qdrant:$qdrant, neo4j:$neo4j, postgres:$postgres}' > results/health_with_hb.json || true
