#!/usr/bin/env bash
set -euo pipefail
echo "[check] MinIO CLI (mc) in PATH"
if ! command -v mc >/dev/null 2>&1; then
  echo "[fail] mc not found. Install: https://min.io/docs/minio/linux/reference/minio-mc.html"
  exit 1
fi
echo "[ok] mc present"

echo "[check] MINIO_URL / MINIO_ACCESS_KEY / MINIO_SECRET_KEY / MINIO_BUCKET"
missing=0
for v in MINIO_URL MINIO_ACCESS_KEY MINIO_SECRET_KEY MINIO_BUCKET; do
  if [ -z "${!v:-}" ]; then
    echo "[fail] $v not set"
    missing=$((missing+1))
  else
    echo "[ok] $v set"
  fi
done
if [ "$missing" -gt 0 ]; then
  echo "[warn] set the missing variables and re-run this checker"
  exit 2
fi

ALIAS="${MINIO_ALIAS:-darfcas}"
echo "[check] mc alias set"
set +e
mc alias set "$ALIAS" "$MINIO_URL" "$MINIO_ACCESS_KEY" "$MINIO_SECRET_KEY" >/dev/null 2>&1
rc=$?
set -e
if [ $rc -ne 0 ]; then
  echo "[fail] could not set mc alias '$ALIAS' to $MINIO_URL"
  exit 3
fi
echo "[ok] mc alias configured: $ALIAS -> $MINIO_URL"

echo "[check] bucket access ($MINIO_BUCKET)"
mc mb "$ALIAS/$MINIO_BUCKET" >/dev/null 2>&1 || true
mc ls "$ALIAS/$MINIO_BUCKET" >/dev/null 2>&1 && echo "[ok] bucket reachable" || { echo "[fail] bucket not reachable"; exit 4; }

echo "[result] MinIO is ready for Phase 7T round-trip"
