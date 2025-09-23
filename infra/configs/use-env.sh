#!/usr/bin/env bash
# Unified environment loader for DARF services
# Loads from standard locations in precedence order

set +u 2>/dev/null || true

# Load in precedence order: local > root > defaults
[ -f ./.env.local ] && { set -a; . ./.env.local; set +a; }
[ -f ./.env ] && { set -a; . ./.env; set +a; }

# Set defaults for core services
: "${MINIO_ENDPOINT:=http://localhost:9000}"
: "${MINIO_ACCESS_KEY:=minioadmin}"
: "${MINIO_SECRET_KEY:=minioadmin}"
: "${QDRANT_URL:=http://localhost:6333}"
: "${NEO4J_URI:=bolt://localhost:7687}"
: "${REDIS_URL:=redis://localhost:6379}"

export MINIO_ENDPOINT MINIO_ACCESS_KEY MINIO_SECRET_KEY
export QDRANT_URL NEO4J_URI REDIS_URL

