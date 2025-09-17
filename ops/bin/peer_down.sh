#!/usr/bin/env bash
set -euo pipefail
printf "===\n===\n===\n"

mapfile -d '' CF < <(bash ops/bin/_compose_files.sh)
echo "[peer_down] compose files:"
for ((i=1;i<${#CF[@]};i+=2)); do echo "  - ${CF[$i]}"; done

set -x
docker compose "${CF[@]}" down
set +x

bash ops/bin/peer_ports_hygiene.sh || true
echo "[peer_down] done"
