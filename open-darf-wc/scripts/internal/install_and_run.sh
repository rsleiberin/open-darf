#!/usr/bin/env bash
set -euo pipefail
printf "===\n===\n===\n"
echo "=== Open-DARF · Install & Run (Linux) ==="
bash ./scripts/run.sh
bash ./scripts/validator_acceptance.sh || true
