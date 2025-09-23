#!/usr/bin/env bash
set -euo pipefail
HOST="${1:-localhost}"
PORT="${2:-6333}"
NAME="${3:-precedents}"
DIM="${4:-1024}"
if ! curl -fsS "http://${HOST}:${PORT}/collections/${NAME}" >/dev/null 2>&1; then
  curl -fsS -X PUT "http://${HOST}:${PORT}/collections/${NAME}" \
    -H 'Content-Type: application/json' \
    -d "{\"vectors\":{\"size\":${DIM},\"distance\":\"Cosine\"}}"
  echo "Created Qdrant collection: ${NAME}"
else
  echo "Qdrant collection exists: ${NAME}"
fi
