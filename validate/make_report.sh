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

HOST=$(hostname -s 2>/dev/null || echo host)
TS=$(date -u +%Y%m%dT%H%M%SZ)
OUT="open-darf-report-${HOST}-${TS}.tar.gz"
echo "[M4] Pack receipts -> ${OUT}"
tar -czf "${OUT}" var/receipts/* || (echo "[warn] no receipts yet"; exit 0)
echo "[ok] ${OUT}"
