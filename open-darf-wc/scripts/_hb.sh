#!/usr/bin/env bash
HB_PID=""
hb_start() {
  local msg="${1:-working}"
  hb_stop || true
  (
    while true; do
      printf "[HB] %s — %(%H:%M:%S)T\n" "$msg" -1
      sleep 2
    done
  ) &
  HB_PID="$!"
  disown "$HB_PID" 2>/dev/null || true
}
hb_stop() {
  if [ -n "${HB_PID:-}" ] && kill -0 "$HB_PID" 2>/dev/null; then
    kill "$HB_PID" 2>/dev/null || true
    wait "$HB_PID" 2>/dev/null || true
  fi
  HB_PID=""
}
trap 'hb_stop; echo; echo "[✖] Cancelled."; exit 130' INT TERM
