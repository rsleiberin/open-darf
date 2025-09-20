#!/usr/bin/env bash
set -euo pipefail

hb(){ printf "[HB] %s — %(%H:%M:%S)T\n" "${1:-working}" -1; }

# Resolve repo root and absolute compose file path
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BASE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
COMPOSE_FILE="${BASE_DIR}/compose.sanitized.yml"

printf "===\n===\n===\n"
echo "=== Open-DARF · Validator Acceptance (Linux, robust Postgres check) ==="

# Discover ports from docker ps
get_port(){ docker ps --format '{{.Names}} {{.Ports}}' | awk -v n="$1" -v cp="$2" ' $1 ~ n { if (match($0, "0\\.0\\.0\\.0:([0-9]+)->"cp"/tcp", m)) {print m[1]; exit} else if (match($0, ":::([0-9]+)->"cp"/tcp", m)) {print m[1]; exit} }'; }

MINIO_API="$(get_port 'minio-1$' 9000)"; [ -z "$MINIO_API" ] && MINIO_API=9000
Q_HTTP="$(get_port '^darf-qdrant-bare$' 6333)"; [ -z "$Q_HTTP" ] && Q_HTTP=6333

# Quick pulses
MINIO_OK=false; curl -fsS "http://localhost:${MINIO_API}/minio/health/live" >/dev/null && MINIO_OK=true
Q_OK=false;     curl -fsS "http://localhost:${Q_HTTP}/healthz" >/dev/null && Q_OK=true

# Ensure postgres service exists / is up under the absolute compose file
PG_CID="$(docker compose -f "${COMPOSE_FILE}" ps -q postgres || true)"
if [ -z "$PG_CID" ]; then
  hb "start postgres (compose.sanitized)"
  docker compose -f "${COMPOSE_FILE}" up -d postgres >/dev/null
  PG_CID="$(docker compose -f "${COMPOSE_FILE}" ps -q postgres || true)"
fi

# Robust PG check ladder:
#  A) pg_isready (no DB args)
#  B) pg_isready with discovered POSTGRES_USER/DB from container env
#  C) psql -U postgres -c "SELECT 1"
PG_OK=false
if [ -n "$PG_CID" ]; then
  # A) simplest readiness
  if docker exec "$PG_CID" pg_isready -q >/dev/null 2>&1; then
    PG_OK=true
  else
    # B) discover envs
    ENV_JSON="$(docker inspect "$PG_CID" --format '{{json .Config.Env}}' 2>/dev/null || echo '[]')"
    POSTGRES_USER="$(echo "$ENV_JSON" | tr -d '[]"' | tr ',' '\n' | awk -F= '/^POSTGRES_USER=/{print $2; exit}')"
    POSTGRES_DB="$(echo   "$ENV_JSON" | tr -d '[]"' | tr ',' '\n' | awk -F= '/^POSTGRES_DB=/{print $2; exit}')"
    # defaults if not present
    [ -z "${POSTGRES_USER:-}" ] && POSTGRES_USER="postgres"
    [ -z "${POSTGRES_DB:-}" ] && POSTGRES_DB="postgres"
    if docker exec "$PG_CID" pg_isready -q -U "$POSTGRES_USER" -d "$POSTGRES_DB" >/dev/null 2>&1; then
      PG_OK=true
    else
      # C) explicit psql query as superuser
      if docker exec "$PG_CID" bash -lc 'psql -U postgres -Atqc "SELECT 1" >/dev/null 2>&1'; then
        PG_OK=true
      fi
    fi
  fi
fi

# Neo4j (bare)
NEO_OK=false; docker exec darf-neo4j cypher-shell -u neo4j -p darf_graph_password "RETURN 1;" >/dev/null 2>&1 && NEO_OK=true

printf "MinIO   : %s\n" "$([ "$MINIO_OK" = true ] && echo ok || echo fail)"
printf "Qdrant  : %s\n" "$([ "$Q_OK" = true ] && echo ok || echo fail)"
printf "Postgres: %s\n" "$([ "$PG_OK" = true ] && echo ok || echo fail)"
printf "Neo4j   : %s\n" "$([ "$NEO_OK" = true ] && echo ok || echo fail)"
PASS=false; $MINIO_OK && $Q_OK && $PG_OK && $NEO_OK && PASS=true
echo "PASS     : $PASS"

# On failure, dump brief diagnostics
if [ "$PASS" != "true" ]; then
  echo "--- postgres logs (tail 100) ---"
  [ -n "$PG_CID" ] && docker logs --tail 100 "$PG_CID" || echo "(no postgres container)"
  echo "--- docker ps (focused) ---"
  docker ps --format 'table {{.Names}}\t{{.Status}}\t{{.Ports}}' | sed -n '1p;/postgres/p;/minio/p;/qdrant/p;/neo4j/p'
fi

$PASS || exit 1
