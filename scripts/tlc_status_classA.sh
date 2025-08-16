#!/usr/bin/env bash
set -Eeuo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUN_DIR="$ROOT/verification/tla/runs"

printf "%-28s %-6s %-10s %-12s %-6s %s\n" "MODULE" "KIND" "DISTINCT" "GENERATED" "DEPTH" "LOG"

find "$RUN_DIR" -type f -name '*.log' -printf '%T@ %p\n' 2>/dev/null \
| sort -n | awk '{print $2}' \
| while read -r log; do
  base="$(basename "$log")"
  kind="$(echo "$base" | sed -E 's/.*_(pos|neg)_.*/\1/')"
  mod="$(echo "$base"  | sed -E 's/_(pos|neg)_[0-9-]+\.log$//')"

  # DISTINCT
  d="$(grep -Eo 'distinct states: *[0-9]+' "$log" | awk '{print $3}' | tail -1 || true)"
  [[ -z "$d" ]] && d="$(grep -Eo '[0-9]+ distinct states found' "$log" | awk '{print $1}' | tail -1 || true)"
  [[ -z "$d" ]] && d="$(grep -Ei 'The number of distinct states: *[0-9]+' "$log" | awk '{print $6}' | tail -1 || true)"

  # GENERATED
  g="$(grep -Eo '([0-9]+) states generated' "$log" | awk '{print $1}' | tail -1 || true)"
  [[ -z "$g" ]] && g="$(grep -Ei 'states generated' "$log" | grep -Eo '[0-9]+' | head -1 || true)"

  # DEPTH
  depth="$(grep -Eo 'depth of the (complete )?state graph (search )?is *[0-9]+' "$log" | awk '{print $NF}' | tail -1 || true)"
  [[ -z "$depth" ]] && depth="$(grep -Eo 'The depth of the complete state graph is *[0-9]+' "$log" | awk '{print $NF}' | tail -1 || true)"

  printf "%-28s %-6s %-10s %-12s %-6s %s\n" "$mod" "$kind" "${d:-?}" "${g:-?}" "${depth:-?}" "$log"
done
