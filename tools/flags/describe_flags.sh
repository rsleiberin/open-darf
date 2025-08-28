#!/usr/bin/env bash
set -Eeo pipefail
ENVF="${1:-var/local/testing.env}"

declare -a KEYS=(
  EXTRACTOR_SCI
  EXTRACTOR_BIO
  EXTRACTOR_TEXT2NKG
  TEMPORAL_GRAPH_MODEL
  RUN_PERF
)

echo "== Flag sources =="
[ -f "$ENVF" ] && echo "local_env=$ENVF" || echo "local_env=absent"
echo "process_env=$SHELL"

echo
printf "%-24s %-10s %-10s\n" "FLAG" "local_env" "process_env"
printf "%-24s %-10s %-10s\n" "----" "---------" "-----------"

for k in "${KEYS[@]}"; do
  le="n/a"
  if [ -f "$ENVF" ]; then
    le="$(grep -E "^${k}=" "$ENVF" | tail -n1 | cut -d= -f2-)"
    [ -z "$le" ] && le="n/a"
  fi
  pe="${!k:-}"
  [ -z "$pe" ] && pe="(unset)"
  printf "%-24s %-10s %-10s\n" "$k" "$le" "$pe"
done

echo
echo "Effective guidance: local env is for developer defaults; process env overrides per shell."
