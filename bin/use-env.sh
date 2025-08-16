#!/usr/bin/env bash
# Unified env loader used across worktrees (MinIO, Qdrant, Neo4j)
set +u 2>/dev/null || true

[ -f ./.env.local ] && { set -a; . ./.env.local; set +a; }

# MinIO (CAS)
: "${MINIO_ENDPOINT:=http://localhost:9100}"
: "${MINIO_ACCESS_KEY:=minioadmin}"
: "${MINIO_SECRET_KEY:=minioadmin}"
: "${MINIO_BUCKET:=anchors}"
: "${MC_HOST_local:=http://minioadmin:minioadmin@localhost:9100}"

# Qdrant (search)
: "${QDRANT_URL:=http://localhost:6333}"
: "${QDRANT_COLLECTION:=anchors}"

# Neo4j (validator)
: "${NEO4J_URL:=bolt://localhost:7687}"
: "${NEO4J_USER:=neo4j}"
: "${NEO4J_PASSWORD:=neo4jpass123}"

echo "[env] MINIO_ENDPOINT=$MINIO_ENDPOINT BUCKET=$MINIO_BUCKET | QDRANT_URL=${QDRANT_URL:-unset} | NEO4J_URL=${NEO4J_URL:-unset}"
