#!/usr/bin/env bash
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
