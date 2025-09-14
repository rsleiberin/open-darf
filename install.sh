#!/usr/bin/env bash

## verbose trace injection (Phase 7R)
if [ "${VERBOSE:-1}" = "1" ]; then
  export PS4="+ $(date +%H:%M:%S).$RANDOM ${BASH_SOURCE##*/}:${LINENO}: "
  set -x
fi
set -euo pipefail

echo "==="
echo "==="
echo "==="

echo "[Phase 7R] BEGIN install umbrella (fail-fast)"

run_stage () {
  local name="$1" script="$2"
  echo "[BEGIN] ${name}"
  set +e
  bash "${script}"
  rc=$?
  set -e
  echo "[END]   ${name} rc=${rc}"
  # rc 41 = environment gate (e.g., WSL)
  if [ "${rc}" -eq 41 ]; then
    echo "[gate] Stopping pipeline early due to environment gate (rc=41)."
    exit 41
  fi
  if [ "${rc}" -ne 0 ]; then
    echo "[error] Stage '${name}' failed (rc=${rc}); aborting."
    exit "${rc}"
  fi
}

run_stage "M1 bootstrap" "install/bootstrap.sh"
run_stage "M2 python_cuda" "install/python_cuda.sh"
run_stage "M3 validator" "validate/run_minimal.sh"
run_stage "M4 make_report" "validate/make_report.sh"

echo "[Phase 7R] END install umbrella"
