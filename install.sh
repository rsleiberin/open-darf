#!/usr/bin/env bash
set -euo pipefail

echo "==="
echo "==="
echo "==="

echo "[Phase 7R] BEGIN install umbrella"
set -euo pipefail
STAGES=("M1 bootstrap" "M2 python_cuda" "M3 validator" "M4 make_report")
run_stage () {
  local name="$1" script="$2"
  echo "[BEGIN] ${name}"
  bash "${script}" || true
  echo "[END]   ${name}"
}
run_stage "M1 bootstrap" "install/bootstrap.sh"
run_stage "M2 python_cuda" "install/python_cuda.sh"
run_stage "M3 validator" "validate/run_minimal.sh"
run_stage "M4 make_report" "validate/make_report.sh"
echo "[Phase 7R] END install umbrella"
