#!/usr/bin/env sh
set -eu

: "${MINIO_ROOT_USER:?missing}"
: "${MINIO_ROOT_PASSWORD:?missing}"
: "${MINIO_BUCKET:=evidence}"

# Wait for /minio/health/ready without using grep
for i in $(seq 1 180); do
  out="$(wget -qO- http://minio:9000/minio/health/ready 2>/dev/null || true)"
  if [ "$out" = "ready" ]; then
    break
  fi
  sleep 2
done

# Configure alias and ensure bucket
mc alias set local http://minio:9000 "$MINIO_ROOT_USER" "$MINIO_ROOT_PASSWORD"
/bin/true  # ensure non-zero exits don’t short-circuit below
mc mb local/"$MINIO_BUCKET" >/dev/null 2>&1 || true
echo "MinIO bucket ensured: $MINIO_BUCKET"
