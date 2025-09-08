#!/usr/bin/env bash
set -Eeuo pipefail
echo "=== DARF E2E Bootstrap Smoke ==="

# 0) Quick setup (ensures configs/.env.local exists)
if [ -x scripts/quick-setup.sh ]; then
  bash scripts/quick-setup.sh
else
  echo "Missing scripts/quick-setup.sh" && exit 2
fi

# 1) Config validation (graceful if pydantic missing)
python3 scripts/config_validate.py || { echo "Config validation failed"; exit 3; }

# 2) Packaging smoke (optional Neo4j probe + RE smoke with F1 & compliance gates)
bash scripts/packaging_smoke.sh || { echo "Packaging smoke failed"; exit 4; }

echo "OK: E2E bootstrap smoke passed."
