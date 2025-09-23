#!/usr/bin/env bash
set -euo pipefail
echo "[peer_ports_hygiene] scanning containers binding 6333/6334"
mapfile -t offenders < <(
  docker ps --format '{{.ID}} {{.Names}} {{.Ports}}' \
  | awk '/(0\.0\.0\.0|127\.0\.0\.1):6333|((0\.0\.0\.0|127\.0\.0\.1):)?6334/ {print $1 "|" $2}'
)
if [[ "${#offenders[@]}" -eq 0 ]]; then
  echo "[peer_ports_hygiene] none"
else
  for line in "${offenders[@]}"; do
    id="${line%%|*}"; name="${line##*|}"
    # Allow our compose-named qdrant through; stop any stragglers
    if [[ "$name" != "darf-qdrant-1" ]]; then
      echo "[peer_ports_hygiene] stop: $name ($id)"
      docker stop "$id" >/dev/null || true
    fi
  done
fi
