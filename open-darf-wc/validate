#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source "./scripts/_hb.sh"

echo "===\n===\n==="
echo "=== Open-DARF · Linux validation with heartbeat ==="

mkdir -p results
hb_start "Collecting system info"
jq -n --arg host "$(hostname)" \
      --arg os "$(uname -a)" \
      --arg docker "$(docker --version 2>/dev/null || echo 'n/a')" \
      --arg ts "$(date -Is)" \
      '{hostname:$host, os:$os, docker:$docker, ts:$ts}' > results/sysinfo.json || true
hb_stop

echo "[1] Health probes with heartbeats…"
HB_MINIO="fail" ; HB_QDRANT="fail"
hb_start "Probing MinIO"
for i in {1..30}; do curl -fsS http://localhost:9000/minio/health/live >/dev/null && { HB_MINIO="ok"; break; } || sleep 2; done
hb_start "Probing Qdrant"
for i in {1..45}; do \
  curl -fsS http://localhost:6333/healthz >/dev/null && { HB_QDRANT="ok"; break; } || sleep 2; \
done || true
hb_stop
jq -n --arg minio "$HB_MINIO" --arg qdrant "$HB_QDRANT" '{minio:$minio,qdrant:$qdrant}' > results/health.json || true

echo "[2] Evidence stub (placeholder until engine emits proofs)…"
hb_start "Generating evidence stub"
NONCE="$(uuidgen 2>/dev/null || cat /proc/sys/kernel/random/uuid)"
SHA256="$(printf '%s' "${NONCE}" | sha256sum | awk '{print $1}')"
jq -n --arg nonce "$NONCE" --arg sha256 "$SHA256" --arg ts "$(date -Is)" \
      '{nonce:$nonce, sha256:$sha256, ts:$ts}' > results/evidence_stub.json || true
hb_stop

echo "[✓] Validation receipts written to results/."
