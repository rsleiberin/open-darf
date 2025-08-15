#!/usr/bin/env bash
set -euo pipefail
shopt -s nullglob
for log in runs/classA-*/tlc.log; do
  fam="$(basename "$(dirname "$log")")"
  if   grep -qE "Invariant .* violated" "$log"; then status="FAIL"
  elif grep -q "^Error:" "$log"; then status="ERROR"
  else status="PASS"; fi
  ds="$(grep -Eo '[0-9]+ distinct states found' "$log" | tail -1 | awk '{print $1}')"
  gen="$(grep -Eo '[0-9,]+ states generated' "$log" | tail -1 | sed 's/,//g' | awk '{print $1}')"
  dep="$(grep -Eo 'depth of the complete state graph search is [0-9]+' "$log" | tail -1 | awk '{print $NF}')"
  echo "$fam: $status (distinct=${ds:-0}, generated=${gen:-0}, depth=${dep:-0})"
done | sort
