#!/usr/bin/env bash
set -euo pipefail
root="verification/tla/runs"
[ -d "$root" ] || { echo "No runs found."; exit 0; }

printf "%-34s | %-8s | %s\n" "MODULE" "KIND" "STATUS"
printf -- "-----------------------------------+----------+-------------------------\n"
for moddir in "$root"/*/; do
  mod=$(basename "$moddir")
  for kind in pos neg; do
    logfile=$(ls -1t "$moddir"/"${mod}"_"${kind}"_*.log 2>/dev/null | head -n1 || true)
    [ -n "${logfile}" ] || { printf "%-34s | %-8s | %s\n" "$mod" "$kind" "—"; continue; }
    if grep -qE 'Error:|Invariant.*violated|Temporal formula.*violated' "$logfile"; then
      status="BITE"
    elif grep -q 'Model checking completed. No error has been found.' "$logfile"; then
      status="PASS"
    else
      status="UNKNOWN"
    fi
    printf "%-34s | %-8s | %s\n" "$mod" "$kind" "$status"
  done
done | sort
