#!/usr/bin/env bash
set +u 2>/dev/null || true
[ -f ./.env.local ] && { set -a; . ./.env.local; set +a; }
echo "[env] QDRANT_URL=${QDRANT_URL:-unset} QDRANT_COLLECTION=${QDRANT_COLLECTION:-unset}"
