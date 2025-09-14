#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
ACC_JSON="$("$ROOT/scripts/phase7i/acceptance_check.py" | tail -n +1)"
status="$(printf '%s\n' "$ACC_JSON" | python3 -c "import sys,json; print(json.load(sys.stdin)['overall_status'])")"
echo "$ACC_JSON"
if [ "$status" = "PASS" ]; then
  echo "[GATE] Phase 7I targets satisfied."
  exit 0
else
  echo "[GATE] Phase 7I targets NOT yet satisfied."
  exit 3
fi
