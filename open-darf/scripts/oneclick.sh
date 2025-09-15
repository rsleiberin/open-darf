#!/usr/bin/env bash
set -euo pipefail

TS="$(date -u +%Y%m%dT%H%M%SZ)"
HOST="$(hostname)"
RECEIPT_DIR="var/receipts/open-darf"
RECEIPT="${RECEIPT_DIR}/oneclick_${HOST}_${TS}.json"
mkdir -p "$RECEIPT_DIR" "var/reports"

status="ok"
reason="completed"

echo "[oneclick] running installer…"
set +e
./install.sh
rc_install=$?
set -e
if [[ $rc_install -ne 0 ]]; then
  status="error"
  reason="install_failed"
fi

echo "[oneclick] doctor probe…"
DOCTOR_OUT="$(./bin/doctor.sh 2>&1 || true)"

echo "[oneclick] minimal validate…"
set +e
./validate/run_minimal.sh > "var/reports/oneclick_run_minimal_${TS}.out" 2>&1
rc_min=$?
set -e
if [[ $rc_min -ne 0 && "$status" == "ok" ]]; then
  status="warn"
  reason="run_minimal_nonzero"
fi

echo "[oneclick] evidence packaging…"
set +e
./validate/generate_evidence.sh
rc_ev=$?
set -e
if [[ $rc_ev -ne 0 && "$status" == "ok" ]]; then
  status="warn"
  reason="evidence_nonzero"
fi

GPU_INFO="$(nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv,noheader 2>/dev/null | tr '\n' ';' || true)"
DISTRO="$( (lsb_release -ds 2>/dev/null || grep -m1 PRETTY_NAME /etc/os-release | cut -d= -f2 | tr -d '\"') || echo unknown )"
KREL="$(uname -r || echo unknown)"
IS_WSL=0
if echo "$KREL" | grep -qi microsoft; then IS_WSL=1; fi
if [[ -n "${WSL_INTEROP:-}" ]]; then IS_WSL=1; fi

{
  echo "{"
  echo "  \"timestamp\": \"${TS}\","
  echo "  \"host\": \"${HOST}\","
  echo "  \"distro\": \"${DISTRO}\","
  echo "  \"kernel\": \"${KREL}\","
  echo "  \"is_wsl\": ${IS_WSL},"
  echo "  \"gpu_info\": \"${GPU_INFO}\","
  echo "  \"steps\": {"
  echo "    \"install_rc\": ${rc_install},"
  echo "    \"run_minimal_rc\": ${rc_min},"
  echo "    \"evidence_rc\": ${rc_ev}"
  echo "  },"
  echo "  \"status\": \"${status}\","
  echo "  \"reason\": \"${reason}\""
  echo "}"
} > "$RECEIPT"

echo "[oneclick] receipt -> $RECEIPT"
exit 0
