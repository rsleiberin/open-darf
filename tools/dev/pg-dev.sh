#!/usr/bin/env bash
# Dev Postgres helper: db-up | db-psql | db-down | db-logs | test-db
set -Ee -o pipefail

# Detect engine
ENGINE=""
if command -v podman >/dev/null 2>&1; then ENGINE="podman"
elif command -v docker >/dev/null 2>&1; then ENGINE="docker"
else echo "Neither podman nor docker found"; exit 1; fi

# Load .env if present
if [[ -f .env ]]; then set -a; . ./.env; set +a; fi

PG_USER="${POSTGRES_USER:-janus}"
PG_PASS="${POSTGRES_PASSWORD:-change_me_dev}"
PG_DB="${POSTGRES_DB:-janus_adr}"
PG_PORT="${POSTGRES_PORT:-5432}"
PG_IMAGE="${POSTGRES_IMAGE:-postgres:15-alpine}"
CONTAINER_NAME="${PG_CONTAINER_NAME:-janus-postgres}"
VOLUME_NAME="${PG_VOLUME_NAME:-janus-pgdata}"

up() {
  # volume
  if [[ "$ENGINE" == "podman" ]]; then
    podman volume inspect "$VOLUME_NAME" >/dev/null 2>&1 || podman volume create "$VOLUME_NAME" >/dev/null
  else
    docker volume inspect "$VOLUME_NAME" >/dev/null 2>&1 || docker volume create "$VOLUME_NAME" >/dev/null
  fi
  # start/run
  if "$ENGINE" ps -a --format '{{.Names}}' | grep -qx "$CONTAINER_NAME"; then
    "$ENGINE" start "$CONTAINER_NAME" >/dev/null || true
  else
    "$ENGINE" run -d --name "$CONTAINER_NAME" \
      -e POSTGRES_USER="$PG_USER" -e POSTGRES_PASSWORD="$PG_PASS" -e POSTGRES_DB="$PG_DB" \
      -p "${PG_PORT}:5432" -v "${VOLUME_NAME}:/var/lib/postgresql/data" "$PG_IMAGE" >/dev/null
  fi
  # readiness
  echo -n "Waiting for Postgres "
  for _ in {1..90}; do
    if "$ENGINE" exec "$CONTAINER_NAME" pg_isready -U "$PG_USER" -d "$PG_DB" -h localhost >/dev/null 2>&1; then
      echo "✓"; return 0
    fi
    echo -n "."; sleep 1
  done
  echo; echo "Postgres not ready"; exit 1
}

psql_shell() {
  "$ENGINE" exec -it -e PGPASSWORD="$PG_PASS" "$CONTAINER_NAME" \
    psql -U "$PG_USER" -d "$PG_DB" -h localhost
}

down() { "$ENGINE" stop "$CONTAINER_NAME" >/dev/null || true; }
logs() { "$ENGINE" logs --tail=200 "$CONTAINER_NAME"; }
test_db() {
  export DATABASE_URL="postgresql://${PG_USER}:${PG_PASS}@127.0.0.1:${PG_PORT}/${PG_DB}"
  pytest -q tests/integration/test_postgres_connection.py
}

case "${1:-}" in
  db-up|up) up ;;
  db-psql|psql) psql_shell ;;
  db-down|down) down ;;
  db-logs|logs) logs ;;
  test-db|test) test_db ;;
  *) echo "Usage: $0 {db-up|db-psql|db-down|db-logs|test-db}"; exit 2 ;;
esac
