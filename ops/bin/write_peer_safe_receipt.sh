#!/usr/bin/env bash
set -euo pipefail

# Inputs via env or args (safe defaults)
PGHOST="${POSTGRES_HOST:-localhost}"
PGPORT="${POSTGRES_PORT:-5540}"
PGUSER="${POSTGRES_USER:-darfuser}"
PGPASS="${POSTGRES_PASSWORD:-darfpass}"
PGDB="${POSTGRES_DB:-darf_audit}"

COMPONENT="${1:-safe_mode_guard}"
ACTION="${2:-peer_probe}"
STATUS="${3:-SUCCESS}"
DURATION_MS="${4:-0}"

export PGPASSWORD="$PGPASS"

psql -h "$PGHOST" -p "$PGPORT" -U "$PGUSER" -d "$PGDB" -v ON_ERROR_STOP=1 <<'PSQL'
BEGIN;

CREATE SCHEMA IF NOT EXISTS audit;

CREATE TABLE IF NOT EXISTS audit.receipts(
  id           BIGSERIAL PRIMARY KEY,
  ts           TIMESTAMPTZ NOT NULL DEFAULT now(),
  component    TEXT NOT NULL,
  action       TEXT NOT NULL,
  status       TEXT NOT NULL,
  details      JSONB NOT NULL DEFAULT '{}'::jsonb,
  duration_ms  INTEGER NOT NULL DEFAULT 0
);

-- Build details JSON on the server side (no client-side expansion)
WITH d AS (
  SELECT jsonb_build_object(
    'context', jsonb_build_object(
      'actor','pipeline',
      'safe_mode', true
    ),
    'host', jsonb_build_object(
      'pg_host', current_setting('server_version', true)
    )
  ) AS j
)
INSERT INTO audit.receipts(component,action,status,details,duration_ms)
SELECT :'COMPONENT', :'ACTION', :'STATUS', (SELECT j FROM d), :'DURATION_MS'::int;

COMMIT;
PSQL
