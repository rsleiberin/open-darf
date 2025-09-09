#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
JSON="$( "$ROOT/scripts/phase7i/acceptance_check.py" )" || true

echo "$JSON" > /tmp/phase7i_gate.json
OVERALL="$(jq -r '.overall_status' /tmp/phase7i_gate.json 2>/dev/null || echo FAIL)"

echo "[GATE] Acceptance overall_status=$OVERALL"
if [ "$OVERALL" = "PASS" ]; then
  echo "[GATE] Phase 7I targets satisfied."
  exit 0
else
  echo "[GATE] Phase 7I targets NOT yet satisfied."
  exit 3
fi
