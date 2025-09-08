#!/usr/bin/env bash
set -Eeuo pipefail
ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT"
VENV=".venv_pure"
if [ -f "$VENV/bin/activate" ]; then
  . "$VENV/bin/activate"
else
  echo "NOTE: $VENV not found. Run scripts/setup_pure_env.sh first (or proceed with deps_missing)."
fi
bash scripts/pure_runner.sh
