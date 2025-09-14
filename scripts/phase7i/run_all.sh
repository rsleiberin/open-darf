#!/usr/bin/env bash
set -euo pipefail
# Minimal orchestrator: runs PURE and PL-Marker over SciERC & BioRED.
# Usage: run_all.sh [--split=test] [--filters=csv]

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
SPLIT="test"
FILTERS=""

for arg in "$@"; do
  case "$arg" in
    --split=*)   SPLIT="${arg#--split=}" ;;
    --filters=*) FILTERS="${arg#--filters=}" ;;
    *) ;; # ignore unknowns (future-proof)
  esac
done

# Preflight gate
"$ROOT/scripts/phase7i/preflight.sh"

models=(pure pl-marker)
datasets=(scierc biored)

for m in "${models[@]}"; do
  for d in "${datasets[@]}"; do
    if [ -n "$FILTERS" ]; then
      "$ROOT/scripts/phase7i/run_bench.sh" "$m" "$d" "$SPLIT" --filters="$FILTERS"
    else
      "$ROOT/scripts/phase7i/run_bench.sh" "$m" "$d" "$SPLIT"
    fi
  done
done

echo "[DONE] All requested baselines executed."
