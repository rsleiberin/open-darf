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
