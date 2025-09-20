# Heartbeat v2 — single-instance, auto-stop, cancel-safe.
# Usage:
#   source "$(dirname "$0")/_hb.sh" || true
#   HB_START "label";   ...cmd... ; HB_STOP
#   HB_WRAP  "label" -- <command args...>
if [ -n "${HB_LIB_V2:-}" ]; then return 0; fi
HB_LIB_V2=1

HB_PID=""
HB_LABEL=""

HB_START() {
  local label="${1:-working}"
  HB_STOP || true
  HB_LABEL="$label"
  (
    while :; do
      printf "[HB] %s — %(%H:%M:%S)T\n" "$HB_LABEL" -1
      sleep 2
    done
  ) & HB_PID="$!"
  disown "$HB_PID" 2>/dev/null || true
}

HB_STOP() {
  if [ -n "${HB_PID:-}" ] && kill -0 "$HB_PID" 2>/dev/null; then
    kill "$HB_PID" >/dev/null 2>&1 || true
    wait "$HB_PID" >/dev/null 2>&1 || true
  fi
  HB_PID=""
  HB_LABEL=""
}

HB_WRAP() {
  # HB_WRAP "label" -- cmd args...
  local label="$1"; shift
  if [ "${1:-}" != "--" ]; then
    echo "[!] HB_WRAP usage: HB_WRAP \"label\" -- command args..." >&2
    return 2
  fi
  shift
  HB_START "$label"
  set +e
  "$@"
  local rc=$?
  set -e
  HB_STOP
  return "$rc"
}

# Stop heartbeats on ^C/TERM/EXIT to avoid runaway loops
__hb_trap(){ HB_STOP; }
trap __hb_trap INT TERM EXIT
