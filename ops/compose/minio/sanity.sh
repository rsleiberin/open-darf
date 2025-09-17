#!/usr/bin/env bash
set -euo pipefail
export MC_HOST_local="${MC_HOST_local:-http://admin:adminadmin@localhost:9000}"
BUCKET="${1:-evidence}"
wget -qO- http://localhost:9000/minio/health/ready | grep -q 'ready'
mc alias set local http://localhost:9000 admin adminadmin
mc mb local/${BUCKET} 2>/dev/null || true
mc ls local/${BUCKET} >/dev/null
echo "MinIO sanity OK; bucket ensured: ${BUCKET}"
