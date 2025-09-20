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

printf "===\n===\n===\n"
echo "=== Open-DARF · Evidence Pack (Linux, heartbeat, cancel-safe) ==="

OUTDIR="evidence_$(hostname)_$(date +%Y%m%dT%H%M%S)"
WORK="results/${OUTDIR}"
mkdir -p "${WORK}"

SERVICES=(darf-minio darf-qdrant darf-postgres darf-neo4j)

hb_start "Collecting docker state"
docker ps --format '{{.ID}}\t{{.Image}}\t{{.Names}}\t{{.Status}}\t{{.Ports}}' > "${WORK}/docker_ps.tsv" || true
docker images --digests --format '{{.Repository}}\t{{.Tag}}\t{{.ID}}\t{{.Digest}}' > "${WORK}/docker_images.tsv" || true
hb_stop

echo "[1] Health checks…"
hb_start "MinIO health"
curl -fsS http://localhost:9000/minio/health/live -o "${WORK}/minio_health.txt" 2>/dev/null || echo "fail" > "${WORK}/minio_health.txt"
hb_start "Qdrant health"
curl -fsS http://localhost:6333/healthz -o "${WORK}/qdrant_health.txt" 2>/dev/null || echo "fail" > "${WORK}/qdrant_health.txt"
hb_start "Postgres ready"
docker exec darf-postgres pg_isready -U darf_user -d darf_audit > "${WORK}/pg_ready.txt" 2>&1 || echo "fail" > "${WORK}/pg_ready.txt"
hb_start "Neo4j bolt"
NEO_RTT="n/a"
t0=$(date +%s%N)
if docker exec darf-neo4j cypher-shell -u neo4j -p darf_graph_password "RETURN 1;" >/dev/null 2>&1; then
  t1=$(date +%s%N); NEO_RTT=$(( (t1 - t0)/1000000 ))
  echo "ok ${NEO_RTT}ms" > "${WORK}/neo4j_bolt.txt"
else
  echo "fail" > "${WORK}/neo4j_bolt.txt"
fi
hb_stop

echo "[2] Recent logs (tail 200)…"
for s in "${SERVICES[@]}"; do
  docker logs --tail 200 "$s" > "${WORK}/${s}_logs_tail.txt" 2>&1 || true
done

echo "[3] Compose & receipts…"
cp -f docker-compose.yml "${WORK}/" 2>/dev/null || true
cp -f docker-compose.override.yml "${WORK}/" 2>/dev/null || true
cp -rf results/*.json "${WORK}/" 2>/dev/null || true

echo "[4] Build MANIFEST.json (robust string args)…"
if command -v jq >/dev/null 2>&1; then
  # Safely read raw text as JSON strings via --arg; auto-escaping handles newlines etc.
  MINIO_TXT="$(tr -d '\r' < "${WORK}/minio_health.txt" || true)"
  QDRANT_TXT="$(tr -d '\r' < "${WORK}/qdrant_health.txt" || true)"
  PG_TXT="$(tr -d '\r' < "${WORK}/pg_ready.txt" || true)"
  NEO_TXT="$(tr -d '\r' < "${WORK}/neo4j_bolt.txt" || true)"
  jq -n \
    --arg ts "$(date -Is)" \
    --arg host "$(hostname)" \
    --arg os "$(uname -a)" \
    --arg docker "$(docker --version 2>/dev/null || echo n/a)" \
    --arg neo_ms "${NEO_RTT}" \
    --arg minio "$MINIO_TXT" \
    --arg qdrant "$QDRANT_TXT" \
    --arg postgres "$PG_TXT" \
    --arg neo4j "$NEO_TXT" \
    '{ts:$ts, host:$host, os:$os, docker:$docker,
      minio:$minio, qdrant:$qdrant, postgres:$postgres, neo4j:$neo4j,
      neo4j_ms: ($neo_ms|tonumber? // null)}' \
    > "${WORK}/MANIFEST.json"
else
  cat > "${WORK}/MANIFEST.json" <<MAN
{"ts":"$(date -Is)","host":"$(hostname)","note":"jq not present; minimal manifest only"}
MAN
fi

echo "[5] Write archive…"
ARCH="results/${OUTDIR}.tar.gz"
tar -czf "${ARCH}" -C "results" "${OUTDIR}"

echo "[✓] Evidence archive:"
echo "    ${ARCH}"
