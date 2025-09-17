#!/usr/bin/env bash
set -euo pipefail
printf "===\n===\n===\n"

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$REPO_ROOT"

declare -a CF
[[ -f ops/compose/compose.yml ]] && CF+=( -f ops/compose/compose.yml )
[[ -f ops/compose/compose.health.yml ]] && CF+=( -f ops/compose/compose.health.yml )
[[ -f ops/compose/compose.override.yml ]] && CF+=( -f ops/compose/compose.override.yml )

echo "Selected compose files:"
if ((${#CF[@]})); then
  for ((j=0; j<${#CF[@]}; j+=2)); do
    echo "  - ${CF[j+1]}"
  done
fi

echo "[peer_up] starting stack"
bash ops/bin/peer_ports_hygiene.sh || true

set -x
docker compose "${CF[@]}" up -d
set +x

echo "[peer_up] waiting for container health (bounded)"
bash ops/bin/peer_health.sh

echo "[peer_up] compose ps (portable)"
docker compose "${CF[@]}" ps

echo "[peer_up] ports (docker ps, darf-*)"
docker ps --format 'table {{.Names}}\t{{.Status}}\t{{.Ports}}' | sed -n '1p;/^darf-/p' || true

echo "[7X] Done."
