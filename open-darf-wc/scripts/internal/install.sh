#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source "./scripts/_hb.sh"

echo "===\n===\n==="
echo "=== Open-DARF · Linux installer with heartbeat ==="

if ! command -v docker >/dev/null; then echo "Docker required."; exit 1; fi
if docker compose version >/dev/null 2>&1; then DC="docker compose"; else DC="docker-compose"; fi
$DC config >/dev/null

echo "[1] Launching core databases (minio/neo4j/qdrant/postgres)…"
hb_start "Starting containers"
$DC up -d minio neo4j qdrant postgres
hb_stop

echo "[2] Waiting for services to report healthy…"
hb_start "Probing MinIO"
for i in {1..30}; do curl -fsS http://localhost:9000/minio/health/live >/dev/null && break || sleep 2; done
hb_start "Probing Qdrant"
for i in {1..45}; do curl -fsS http://localhost:6333/healthz >/dev/null && break || sleep 2; done || true
hb_start "Probing Neo4j (HTTP splash)"
for i in {1..60}; do curl -fsS -I http://localhost:7474 >/dev/null && break || sleep 2; done || true
hb_stop
echo "[✓] Databases up. Start engine with: $DC up -d darf-engine"
