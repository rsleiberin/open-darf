#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
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
  if grep -RIl --exclude-dir=.git --exclude-dir=node_modules -e "$p" . >/dev/null 2>&1; then
    echo "  [hit] $p"
    hit=1
  fi
done
[ "$hit" -eq 0 ] && echo "[ok] No forbidden phrases found." || { echo "[fail] Forbidden phrases detected."; exit 3; }
