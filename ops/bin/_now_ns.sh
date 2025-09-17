#!/usr/bin/env bash
set -euo pipefail
# Prefer nanoseconds; fall back to ms
if date +%s%N >/dev/null 2>&1; then
  date +%s%N
else
  echo "$(( $(date +%s) * 1000000000 ))"
fi
