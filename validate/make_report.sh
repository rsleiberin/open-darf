#!/usr/bin/env bash
set -euo pipefail

echo "==="
echo "==="
echo "==="

HOST="$(hostname -s || echo host)"
TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUT="open-darf-report-${HOST}-${TS}.tar.gz"

echo "[M4] BEGIN make_report → ${OUT}"

# Pick the most recent receipts dir
LATEST="$(find var/receipts -mindepth 1 -maxdepth 1 -type d 2>/dev/null | sort | tail -n 1)"
if [ -z "${LATEST}" ]; then
  echo "[warn] no receipts found; creating empty report scaffold"
  mkdir -p var/receipts/_empty
  LATEST="var/receipts/_empty"
fi

# Pack: receipts + daily status doc + validator script hash provenance
tar -czf "${OUT}" \
  "${LATEST}" \
  docs/status/phase7r_daily.md \
  validate/minimal_validator.py \
  tools/gpu_diag.sh tools/torch_diag.py tools/peek_receipts.sh 2>/dev/null || true

echo "[M4] Report created: ${OUT}"
echo "[M4] END make_report"
