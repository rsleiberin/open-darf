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

echo "[M3] BEGIN minimal validator"
TS=$(date -u +%Y%m%dT%H%M%SZ); OUTDIR="var/receipts/${TS}"; mkdir -p "${OUTDIR}"
python validate/minimal_validator.py | tee "${OUTDIR}/validator_stdout.log"
echo "[M3] END minimal validator"
