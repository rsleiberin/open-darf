#!/usr/bin/env bash
set -euo pipefail

ts="$(date -Is)"
epoch="$(date +%s)"
out_dir="docs/evidence/peers"
mkdir -p "$out_dir"

name="peer_readiness_${epoch}.json"
path="${out_dir}/${name}"

# Helper to fetch container state/health/ports
probe_container () {
  local n="$1"
  local state health ports
  state="$(docker inspect -f '{{.State.Status}}' "$n" 2>/dev/null || echo unknown)"
  health="$(docker inspect -f '{{if .State.Health}}{{.State.Health.Status}}{{end}}' "$n" 2>/dev/null || true)"
  ports="$(docker ps --filter name="^/$n$" --format '{{.Ports}}')"
  printf '"%s":{"state":"%s","health":"%s","ports":"%s"}' "$n" "$state" "${health:-}" "${ports//\"/\\\"}"
}

# Live probes (host-level)
probe_http () { curl -fsS "$1" >/dev/null 2>&1 && echo ok || echo fail; }
probe_port () {
  local host="$1" port="$2"
  if command -v nc >/dev/null 2>&1; then
    nc -z "$host" "$port" >/dev/null 2>&1 && echo ok || echo fail
  else
    bash -c "exec 3<>/dev/tcp/${host}/${port}" >/dev/null 2>&1 && echo ok || echo fail
  fi
}

# Compose JSON
{
  echo -n '{'
  printf '"timestamp":"%s",' "$ts"
  printf '"host":"%s",' "$(hostname)"
  printf '"services":{'
  s1="$(probe_container darf-postgres-1)"; echo -n "$s1,"
  s2="$(probe_container darf-neo4j-1)";   echo -n "$s2,"
  s3="$(probe_container darf-minio-1)";   echo -n "$s3,"
  s4="$(probe_container darf-qdrant-1)";  echo -n "$s4"
  echo -n '},'
  echo -n '"live":{'
  # host port mappings from your current compose
  printf '"qdrant_http":"%s",'  "$(probe_http  http://127.0.0.1:6333/)"
  printf '"qdrant_grpc":"%s",'  "$(probe_port 127.0.0.1 6500)"
  printf '"neo4j_http":"%s",'   "$(probe_http  http://127.0.0.1:7575/)"
  printf '"neo4j_bolt":"%s",'   "$(probe_port 127.0.0.1 7787)"
  printf '"minio_api":"%s",'    "$(probe_port 127.0.0.1 9010)"
  printf '"minio_console":"%s",' "$(probe_port 127.0.0.1 9110)"
  printf '"postgres_tcp":"%s"'  "$(probe_port 127.0.0.1 5540)"
  echo -n '}'
  echo -n '}'
} > "$path"

# Human summary
echo "[readiness] wrote: $path"
grep -o '"live":{[^}]*}' "$path" | sed 's/","/"\n  "/g; s/{"live":{//; s/}//; s/"/  /g'
