#!/usr/bin/env bash
set -euo pipefail
printf "===\n===\n===\n"
echo "=== Open-DARF · Port Inspector ==="
PORTS=(7474 7687 6333 6334 9000 9001 5432)
for p in "${PORTS[@]}"; do
  echo "-- :$p --"
  ss -ltnp "( sport = :$p )" 2>/dev/null | awk 'NR==1{next}{print}' || true
  command -v lsof >/dev/null 2>&1 && lsof -i :"$p" -n -P 2>/dev/null | sed -e '1,1d' || true
done
