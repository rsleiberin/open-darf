#!/usr/bin/env bash
set -euo pipefail

DEADLINE="${PEER_HEALTH_DEADLINE:-30}"
INTERVAL="${PEER_HEALTH_INTERVAL:-3}"

start_ts=$(date +%s)
end_ts=$(( start_ts + DEADLINE ))

targets=(darf-qdrant-1 darf-neo4j-1 darf-postgres-1 darf-minio-1)
last_line=""

short_state () {
  local name="$1"
  local state health
  state="$(docker inspect -f '{{.State.Status}}' "$name" 2>/dev/null || echo unknown)"
  health="$(docker inspect -f '{{if .State.Health}}{{.State.Health.Status}}{{end}}' "$name" 2>/dev/null || true)"
  if [[ -n "$health" ]]; then
    echo "$health"
  else
    echo "$state"
  fi
}

while (( $(date +%s) < end_ts )); do
  ready=0; total=0; summary=()

  for t in "${targets[@]}"; do
    if ! docker inspect "$t" >/dev/null 2>&1; then
      continue
    fi
    total=$((total+1))
    s="$(short_state "$t")"

    if [[ "$t" == "darf-qdrant-1" ]]; then
      if curl -fsS http://127.0.0.1:6333/ >/dev/null 2>&1; then
        ((ready++))
        s="${s}+http"
      fi
    else
      if [[ "$s" == "healthy" || "$s" == "running" ]]; then
        ((ready++))
      fi
    fi
    summary+=("${t#darf-}:${s}")
  done

  line="[peer_health] ${ready}/${total} ready  ${summary[*]}"
  if [[ "$line" != "$last_line" ]]; then
    echo "$line"
    last_line="$line"
  fi

  (( total>0 && ready==total )) && exit 0
  sleep "$INTERVAL"
done

echo "[peer_health] deadline reached: ${last_line:-no containers found}"
exit 0
