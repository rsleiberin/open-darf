#!/usr/bin/env bash
set -euo pipefail

names=(darf-postgres-1 darf-neo4j-1 darf-minio-1 darf-qdrant-1)
echo -n '{'
first=1
for n in "${names[@]}"; do
  if ! docker inspect "$n" >/dev/null 2>&1; then
    continue
  fi
  state="$(docker inspect -f '{{.State.Status}}' "$n" 2>/dev/null || echo unknown)"
  health="$(docker inspect -f '{{if .State.Health}}{{.State.Health.Status}}{{end}}' "$n" 2>/dev/null || true)"
  ports="$(docker ps --filter name="^/$n$" --format '{{.Ports}}')"
  [[ $first -eq 0 ]] && echo -n ','
  first=0
  printf '"%s":{"state":"%s","health":"%s","ports":"%s"}' "$n" "$state" "${health:-}" "${ports//\"/\\\"}"
done
echo '}'
