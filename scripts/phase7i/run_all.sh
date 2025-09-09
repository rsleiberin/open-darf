#!/usr/bin/env bash
set -euo pipefail
SPLIT="test"
FILTERS=""
while [ $# -gt 0 ]; do
  case "$1" in
    --split=*)   SPLIT="${1#--split=}" ;;
    --filters=*) FILTERS="${1#--filters=}" ;;
  esac
  shift || true
done

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
RUN="$ROOT/scripts/phase7i/run_bench.sh"

declare -a CMDS=(
  "pure scierc"
  "pure biored"
  "pl-marker scierc"
  "pl-marker biored"
)

for C in "${CMDS[@]}"; do
  set -- $C
  M="$1"; D="$2"
  echo "[RUN] $M on $D split=$SPLIT filters=${FILTERS:-<none>}"
  "$RUN" "$M" "$D" --split="$SPLIT" ${FILTERS:+--filters="$FILTERS"} || true
done

echo "[DONE] All requested baselines executed."
