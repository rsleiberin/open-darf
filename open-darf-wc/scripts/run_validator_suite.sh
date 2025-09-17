#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source "./scripts/_hb.sh"

printf "===\n===\n===\n"
echo "=== Open-DARF · Validator Suite Runner (Linux) ==="

# Optional: start stack if not running
need_start=0
for n in darf-minio darf-qdrant darf-postgres darf-neo4j; do
  docker ps -q --filter "name=^${n}$" | grep -q . || { need_start=1; break; }
done
if [ "$need_start" -eq 1 ]; then
  echo "[Info] Stack not fully running; starting via scripts/run.sh"
  bash ./scripts/run.sh
fi

# Run acceptance
bash ./scripts/validator_acceptance.sh
