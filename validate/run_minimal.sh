#!/usr/bin/env bash
set -euo pipefail

echo "==="
echo "==="
echo "==="

echo "[M3] BEGIN run_minimal (non-fatal visibility)"

TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUTDIR="var/receipts/${TS}_validator"
mkdir -p "$OUTDIR"

export VALIDATOR_OUTDIR="$OUTDIR"

set +e
python3 validate/minimal_validator.py | tee "$OUTDIR/validator.console.out"
VAL_RC=${PIPESTATUS[0]}
set -e

echo "${VAL_RC}" > "$OUTDIR/validator.rc"

echo "[M3] validator rc=${VAL_RC}"
echo "[M3] END run_minimal"
exit 0
