#!/usr/bin/env bash
set -Eeuo pipefail
echo "=== DARF Lifecycle Smoke ==="
# 1) Validate config surface (graceful if pydantic missing)
python3 scripts/config_validate.py || { echo "Config validation failed"; exit 2; }
# 2) Check for key artifacts
for p in packages/darf_config/settings.py compose/compose.yaml configs/.env.sample; do
  [ -f "$p" ] || { echo "Missing artifact: $p"; exit 3; }
done
echo "OK: config validated & artifacts present."
