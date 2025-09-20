# DO NOT COMMIT THIS FILE — PREVIEW OF PROPOSED HEADER
# Header: Purpose
# One or two plain sentences describing what this file does and who runs it.

# Header: Inputs
# - Environment variables / CLI flags
# - External services called (if any)

# Header: Outputs
# - Files/receipts generated
# - Network side effects (ports/endpoints touched)

# Header: Data Flow
# Source → Transform/Validation → Sink (mention receipts directory)

# Header: Failure Modes & Recovery
# Common errors, detection cues, and operator actions.

# Header: Idempotence & Teardown
# What is safe to re-run; cleanup behavior.

# Header: Security & Privacy Notes
# Sensitive ops (if any). Stays local unless explicit user consent for publishing evidence.

#!/usr/bin/env bash
set -euo pipefail
printf "===\n===\n===\n"
echo "=== Open-DARF · Kill Switch & Cleanup (cancel-safe) ==="
WS="${WS:-$PWD/open-darf-wc}"
RESULTS="$WS/results"; mkdir -p "$RESULTS"
ITER_MAX="${ITER_MAX:-5}"     # bounded post-check time
PRUNE_VOLUMES="${PRUNE_VOLUMES:-0}"
PRUNE_IMAGES="${PRUNE_IMAGES:-0}"

HB_PID=""
hb_start(){ local msg="${1:-working}"; hb_stop || true; ( while true; do printf "[HB] %s — %(%H:%M:%S)T\n" "$msg" -1; sleep 2; done ) & HB_PID="$!"; disown "$HB_PID" 2>/dev/null || true; }
hb_stop(){ if [ -n "${HB_PID:-}" ] && kill -0 "$HB_PID" 2>/dev/null; then kill "$HB_PID" 2>/dev/null || true; wait "$HB_PID" 2>/dev/null || true; fi; HB_PID=""; }
trap 'hb_stop; echo; echo "[✖] Cancelled."; exit 130' INT TERM

NAME_RE='^darf-(neo4j|qdrant|minio|postgres)(-1)?$'
NET_RE='^open-darf_default$'
VOL_RE='^open-darf_(neo4j|qdrant|minio|postgres)_(data|logs)$'
PORTS=(7474 7687 6333 6334 9000 9001 5432)

echo "[0] Snapshot:"
docker ps -a --format '{{.Names}}\t{{.Status}}\t{{.Ports}}' | grep -E "$NAME_RE" || echo "(none)"
echo "[0.1] Ports:"
for p in "${PORTS[@]}"; do printf "  :%s -> " "$p"; ss -ltnp "( sport = :$p )" 2>/dev/null | awk 'NR==1{next}{print}'; done

echo "[1] Stop & remove containers…"
hb_start "stopping containers"
mapfile -t IDS < <(docker ps -a -q --format '{{.ID}}\t{{.Names}}' | awk -v re="$NAME_RE" '$2~re{print $1}')
[ "${#IDS[@]}" -gt 0 ] && docker stop "${IDS[@]}" >/dev/null 2>&1 || true
[ "${#IDS[@]}" -gt 0 ] && docker rm   "${IDS[@]}" >/dev/null 2>&1 || true
hb_stop

echo "[2] Remove compose orphans & network…"
hb_start "compose down"
( cd "$WS" 2>/dev/null && (docker compose down --remove-orphans || docker-compose down --remove-orphans) >/dev/null 2>&1 ) || true
hb_stop
hb_start "remove network"
mapfile -t NETS < <(docker network ls --format '{{.Name}}' | grep -E "$NET_RE" || true)
[ "${#NETS[@]}" -gt 0 ] && docker network rm "${NETS[@]}" >/dev/null 2>&1 || true
hb_stop

if [ "$PRUNE_VOLUMES" = "1" ]; then
  echo "[3] Removing DARF volumes (DATA LOSS)…"
  hb_start "remove volumes"
  mapfile -t VOLS < <(docker volume ls --format '{{.Name}}' | grep -E "$VOL_RE" || true)
  [ "${#VOLS[@]}" -gt 0 ] && docker volume rm "${VOLS[@]}" >/dev/null 2>&1 || true
  hb_stop
else
  echo "[3] Volumes preserved (set PRUNE_VOLUMES=1 to delete)."
fi

[ "$PRUNE_IMAGES" = "1" ] && { echo "[3.1] Pruning dangling images…"; hb_start "image prune"; docker image prune -f >/dev/null 2>&1 || true; hb_stop; }

echo "[4] Post-clean peek (max $((ITER_MAX*2))s)…"
for i in $(seq 1 "$ITER_MAX"); do
  hb_start "post-clean $i/$ITER_MAX"
  docker ps --format '{{.Names}}\t{{.Status}}\t{{.Ports}}' | grep -E "$NAME_RE" || echo "(none)"
  for p in "${PORTS[@]}"; do printf "  :%s -> " "$p"; ss -ltnp "( sport = :$p )" 2>/dev/null | awk 'NR==1{next}{print}'; done
  sleep 2; hb_stop
done

echo "[✓] Cleanup complete."
