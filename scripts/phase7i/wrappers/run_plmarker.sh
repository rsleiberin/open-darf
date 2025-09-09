#!/usr/bin/env bash
# Hardened PL-Marker wrapper: ensure Bash, probe candidate commands, pass through args.
set -Eeuo pipefail

# If not running under bash, re-exec with bash (guards against /bin/sh)
if [ -z "${BASH_VERSION:-}" ]; then
  exec /usr/bin/env bash "$0" "$@"
fi

CANDIDATES=(
  "python -m plmarker.run"
  "python -m PLMarker.run"
  "pl-marker"
)

choose_runner() {
  local c
  for c in "${CANDIDATES[@]}"; do
    if ${c} --help >/dev/null 2>&1; then
      echo "${c}"
      return 0
    fi
  done
  echo "${CANDIDATES[0]}"
  return 1
}

RUN_CMD="$(choose_runner || true)"
echo "[PL-Marker] Using command: ${RUN_CMD}" >&2

# shellcheck disable=SC2086
eval ${RUN_CMD} "$@"
