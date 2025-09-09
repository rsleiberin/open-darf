#!/usr/bin/env bash
# Hardened PURE wrapper: ensure Bash, probe candidate commands, pass through args.
set -Eeuo pipefail

# If not running under bash, re-exec with bash (guards against /bin/sh)
if [ -z "${BASH_VERSION:-}" ]; then
  exec /usr/bin/env bash "$0" "$@"
fi

# Candidate launchers (first that responds to --help is chosen best-effort)
CANDIDATES=(
  "python -m pure.run"
  "python -m PURE.run"
  "pure"
)

choose_runner() {
  local c
  for c in "${CANDIDATES[@]}"; do
    # Best-effort help probe; rc can be non-zero, just look for any output
    if ${c} --help >/dev/null 2>&1; then
      echo "${c}"
      return 0
    fi
  done
  # If none respond, still prefer first candidate for an honest attempt
  echo "${CANDIDATES[0]}"
  return 1
}

RUN_CMD="$(choose_runner || true)"

# Log for harness diagnostics
echo "[PURE] Using command: ${RUN_CMD}" >&2

# Execute with all original args; rely on harness to supply --dataset/--split/etc.
# shellcheck disable=SC2086
eval ${RUN_CMD} "$@"
