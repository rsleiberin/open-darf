#!/usr/bin/env bash
set -Eeo pipefail
# Enforce service-free defaults on CI by requiring flags == 0 or unset.
declare -a KEYS=(
  EXTRACTOR_SCI
  EXTRACTOR_BIO
  EXTRACTOR_TEXT2NKG
  TEMPORAL_GRAPH_MODEL
  RUN_PERF
)
FAIL=0
for k in "${KEYS[@]}"; do
  v="${!k:-0}"
  if [ "$v" != "0" ]; then
    echo "❌ $k must be 0 on CI (was '$v')"
    FAIL=1
  else
    echo "✓ $k=0"
  fi
done
[ "$FAIL" -eq 0 ] && echo "CI service-free flags verified" || exit 1
