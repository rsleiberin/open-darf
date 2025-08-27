#!/usr/bin/env bash
set -eE -o pipefail
trap - ERR EXIT RETURN DEBUG || true

ENV_FILE="${1:-var/local/testing.env}"
ACTION="${2:-status}"
FLAG="${3:-all}"

ensure_line () {
  local key="$1" val="$2"
  grep -q "^export ${key}=" "$ENV_FILE" 2>/dev/null || echo "export ${key}=${val}" >> "$ENV_FILE"
}

set_flag () {
  local key="$1" val="$2"
  ensure_line "$key" "$val"
  # portable in-place edit
  tmp="${ENV_FILE}.tmp.$$"
  awk -v k="$key" -v v="$val" 'BEGIN{done=0} { if($0 ~ "^export "k"="){ print "export "k"="v; done=1 } else { print } } END{ if(done==0){ print "export "k"="v } }' "$ENV_FILE" > "$tmp"
  mv "$tmp" "$ENV_FILE"
}

status () {
  echo "# Feature flags in $ENV_FILE"
  grep -E "^export (EXTRACTOR_|TEMPORAL_GRAPH_MODEL|RUN_PERF)" "$ENV_FILE" 2>/dev/null || echo "(no flags yet)"
}

toggle_all () {
  local val="$1"
  for k in EXTRACTOR_SCI EXTRACTOR_BIO EXTRACTOR_TEXT2NKG TEMPORAL_GRAPH_MODEL; do
    set_flag "$k" "$val"
  done
}

case "$ACTION" in
  enable)
    if [ "$FLAG" = "all" ]; then toggle_all 1; else set_flag "$FLAG" 1; fi
    status
    ;;
  disable)
    if [ "$FLAG" = "all" ]; then toggle_all 0; else set_flag "$FLAG" 0; fi
    status
    ;;
  status|*)
    status
    ;;
esac
