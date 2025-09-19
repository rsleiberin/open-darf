#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/_hb.sh" || true
printf "===\n===\n===\n"
echo "=== Open-DARF · Run (Linux) — compose DBs + bare Neo4j ==="

# Compose-up DBs (MinIO/Qdrant/Postgres)
HB_WRAP "compose up (DB)" -- bash -lc '
  docker compose up -d minio qdrant postgres
'

# Bare-run Neo4j (clean & fast path), idempotent
HB_WRAP "neo4j (bare-run)" -- bash -lc '
  docker rm -f darf-neo4j >/dev/null 2>&1 || true
  docker run -d --name darf-neo4j --restart unless-stopped \
    -p 7474:7474 -p 7687:7687 \
    -e NEO4J_AUTH=neo4j/darf_graph_password \
    neo4j:5.15-community >/dev/null
'

# Quick health pulses (bounded, no loops)
HB_START "health pulses"
curl -fsS http://localhost:9000/minio/health/live >/dev/null && echo "MinIO: ok" || echo "MinIO: fail"
curl -fsS http://localhost:6333/healthz            >/dev/null && echo "Qdrant: ok" || echo "Qdrant: fail"
docker exec darf-postgres pg_isready -U darf_user -d darf_audit >/dev/null 2>&1 && echo "Postgres: ok" || echo "Postgres: fail"
sleep 1
HB_STOP

# Neo4j ping
HB_WRAP "neo4j ping" -- bash -lc '
  docker exec darf-neo4j cypher-shell -u neo4j -p darf_graph_password "RETURN 1;" >/dev/null
  echo "Neo4j: ok"
'
