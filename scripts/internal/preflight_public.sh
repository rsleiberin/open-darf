#!/usr/bin/env bash
set -euo pipefail
echo "[preflight] Starting public checks."

# Compose guard
if env | grep -qiE '(^|_)AUTO_COMPOSE_UP=1'; then
  echo "[guard] AUTO_COMPOSE_UP=1 is not allowed."
  exit 2
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

# Contamination
if [ -x "scripts/internal/contamination_check.sh" ]; then
  scripts/internal/contamination_check.sh
else
  echo "[info] contamination_check.sh not found."
fi

# Fence linter
if [ -x "scripts/lint_no_triple_backticks.sh" ]; then
  echo "[lint] Running markdown fence policy check."
  scripts/lint_no_triple_backticks.sh || {
    echo "[warn] Fence linter reported issues."
  }
else
  echo "[info] No fence linter found."
fi

# Env (non-fatal)
if [ -x "scripts/internal/env_check.sh" ]; then
  echo "[env] Running environment check (STRICT_ENV=${STRICT_ENV:-0})."
  scripts/internal/env_check.sh || true
fi

echo "[preflight] Completed."
