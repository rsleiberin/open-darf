#!/usr/bin/env bash
set -Eeuo pipefail
ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT"
mkdir -p configs
if [ ! -f configs/.env.local ]; then
  cp configs/.env.sample configs/.env.local
  echo "Created configs/.env.local from sample."
else
  echo "configs/.env.local already exists."
fi
echo "To validate (if pydantic installed): python3 scripts/config_validate.py"
