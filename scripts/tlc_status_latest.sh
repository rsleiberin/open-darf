#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUN_DIR="$ROOT/verification/tla/runs"

printf "%-28s %-6s %-10s %-12s %-6s %s\n" "MODULE" "KIND" "DISTINCT" "GENERATED" "DEPTH" "LOG"

declare -A latest

# Build latest log per {module, kind}
while IFS= read -r line; do
  [[ -z "$line" ]] && continue
  ts="${line%% *}"
  path="${line#* }"
  base="$(basename "$path")"
  if [[ "$base" =~ _(pos|neg)_([0-9-]+)\.log$ ]]; then
    kind="${BASH_REMATCH[1]}"
    mod="${base%_${kind}_*}"
    key="$mod|$kind"
    prev="${latest[$key]:-0 }"
    prev_ts="${prev%% *}"
    if [[ "$(printf '%0.6f\n' "$ts")" > "$(printf '%0.6f\n' "$prev_ts")" ]]; then
      latest[$key]="$ts $path"
    fi
  fi
done < <(find "$RUN_DIR" -type f -name '*.log' -printf '%T@ %p\n' 2>/dev/null | sort -n)

# Extract fields and print
for key in "${!latest[@]}"; do
  log="${latest[$key]#* }"
  base="$(basename "$log")"
  [[ "$base" =~ _(pos|neg)_ ]] || continue
  kind="${BASH_REMATCH[1]}"
  mod="${base%_${kind}_*}"

  d="$(grep -Eo 'distinct states: *[0-9]+' "$log" | awk '{print $3}' | tail -1 || true)"
  [[ -z "$d" ]] && d="$(grep -Eo '[0-9]+ distinct states found' "$log" | awk '{print $1}' | tail -1 || true)"
  [[ -z "$d" ]] && d="$(grep -Ei 'The number of distinct states: *[0-9]+' "$log" | awk '{print $6}' | tail -1 || true)"

  g="$(grep -Eo '([0-9]+) states generated' "$log" | awk '{print $1}' | tail -1 || true)"
  [[ -z "$g" ]] && g="$(grep -Ei 'states generated' "$log" | grep -Eo '[0-9]+' | head -1 || true)"

  depth="$(grep -Eo 'depth of the (complete )?state graph (search )?is *[0-9]+' "$log" | awk '{print $NF}' | tail -1 || true)"
  [[ -z "$depth" ]] && depth="$(grep -Eo 'The depth of the complete state graph is *[0-9]+' "$log" | awk '{print $NF}' | tail -1 || true)"

  printf "%-28s %-6s %-10s %-12s %-6s %s\n" "$mod" "$kind" "${d:-?}" "${g:-?}" "${depth:-?}" "$log"
done
