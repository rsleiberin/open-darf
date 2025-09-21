#!/usr/bin/env bash
set -euo pipefail
strict="${STRICT_ENV:-0}"
fail(){ echo "[env] $1"; [ "$strict" = "1" ] && exit 2 || true; }
: "${NEO4J_PASSWORD:=}"; [ -z "$NEO4J_PASSWORD" ] && fail "NEO4J_PASSWORD is empty; set it in .env"
: "${POSTGRES_PASSWORD:=}"; [ -z "$POSTGRES_PASSWORD" ] && fail "POSTGRES_PASSWORD is empty; set it in .env"
echo "[env] Check complete."
