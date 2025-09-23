#!/usr/bin/env bash
# safe_timeout.sh — validates duration and falls back if `timeout` is missing
set -euo pipefail

if [[ $# -lt 2 ]]; then
  echo "Usage: safe_timeout.sh <duration> <cmd> [args...]" >&2
  exit 2
fi

DUR_RAW="$1"; shift

# Normalize duration: accept "12", "12s". Reject others but continue safely.
if [[ "$DUR_RAW" =~ ^[0-9]+$ ]]; then
  SECS="$DUR_RAW"
elif [[ "$DUR_RAW" =~ ^([0-9]+)s$ ]]; then
  SECS="${BASH_REMATCH[1]}"
else
  echo "safe_timeout: non-numeric duration '$DUR_RAW' — running without timeout (no crash)" >&2
  exec "$@"
fi

# Prefer GNU timeout if available
if command -v timeout >/dev/null 2>&1; then
  exec timeout -s TERM "${SECS}s" "$@"
fi

# Fallback: implement a soft timeout in bash
"$@" &
CHILD_PID=$!
(
  sleep "${SECS}" || true
  if kill -0 "$CHILD_PID" 2>/dev/null; then
    kill -TERM "$CHILD_PID" 2>/dev/null || true
  fi
) &
WATCH_PID=$!

# Ensure no orphan
cleanup(){ kill -TERM "$WATCH_PID" 2>/dev/null || true; }
trap cleanup EXIT

wait "$CHILD_PID" || {
  # If the child was killed by us, emulate timeout's exit 124
  exit 124
}
