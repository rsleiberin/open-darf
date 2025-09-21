#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

SELF_PATH="scripts/internal/contamination_check.sh"
SELF_BASENAME="$(basename "$SELF_PATH")"

patterns=(
  "Implementation Agent"
  "Architect handoff"
  "architect handoff"
  "handoff"
  "Phase "
  "internal templates"
  "scaffolded by"
  "Addendum"
)

echo "[check] Scanning repository for forbidden phrases..."
hit=0
for p in "${patterns[@]}"; do
  if grep -RIl \
      --exclude-dir=.git \
      --exclude-dir=.github \
      --exclude-dir=node_modules \
      --exclude-dir=results \
      --exclude-dir=evidence \
      --exclude-dir=var \
      --exclude="${SELF_BASENAME}" \
      --exclude="${SELF_PATH}" \
      -e "$p" . >/dev/null 2>&1; then
    echo "  [hit] $p"
    hit=1
  fi
done

if [ "$hit" -eq 0 ]; then
  echo "[ok] No forbidden phrases found."
else
  echo "[fail] Forbidden phrases detected. See hits above."
  exit 3
fi
