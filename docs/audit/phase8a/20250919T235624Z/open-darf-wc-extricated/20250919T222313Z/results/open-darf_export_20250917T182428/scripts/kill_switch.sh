#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/_hb.sh" || true
printf "===\n===\n===\n"
echo "=== Open-DARF · Kill Switch (cancel-safe) ==="
HB_WRAP "compose down" -- bash -lc 'docker compose down --remove-orphans || true'
HB_WRAP "stop non-compose" -- bash -lc 'docker rm -f darf-neo4j >/dev/null 2>&1 || true'
echo "[✓] All DARF containers stopped."
