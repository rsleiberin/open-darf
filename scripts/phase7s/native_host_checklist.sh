#!/usr/bin/env bash
set -euo pipefail

TS="$(date -u +%Y%m%dT%H%M%SZ)"
HOST="$(hostname)"
RECEIPT="var/receipts/phase7s/native_check_${HOST}_${TS}.json"
mkdir -p "var/receipts/phase7s" "var/reports"

printf "===\n===\n===\n"
echo "[native-check] gating environment for Ubuntu 22.04 + RTX 30/40"

DISTRO="$( (lsb_release -ds 2>/dev/null || grep -m1 PRETTY_NAME /etc/os-release | cut -d= -f2 | tr -d '\"') || echo unknown )"
UBU_VER="$( (lsb_release -rs 2>/dev/null) || echo "" )"
KREL="$(uname -r || echo unknown)"
IS_WSL=0
if echo "$KREL" | grep -qi microsoft; then IS_WSL=1; fi
if [[ -n "${WSL_INTEROP:-}" ]]; then IS_WSL=1; fi

GPU_INFO="$(nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv,noheader 2>/dev/null | tr '\n' ';' || true)"
HAS_GPU=0
[[ -n "$GPU_INFO" ]] && HAS_GPU=1

ok_gate=1
reason="ok"
if [[ "$UBU_VER" != "22.04" && "$DISTRO" != *"22.04"* ]]; then
  ok_gate=0; reason="not_ubuntu_22_04"
fi
if [[ $IS_WSL -eq 1 ]]; then
  ok_gate=0; reason="wsl_env"
fi
if [[ $HAS_GPU -ne 1 ]]; then
  ok_gate=0; reason="no_gpu_detected"
fi

echo "[native-check] distro=$DISTRO ubuntuv=$UBU_VER kernel=$KREL wsl=$IS_WSL gpu=$HAS_GPU :: $GPU_INFO"

install_rc=null; run_rc=null; ev_rc=null
if [[ $ok_gate -eq 1 ]]; then
  echo "[native-check] gate PASSED — running installer, minimal validate, evidence"
  set +e
  ./install.sh
  install_rc=$?
  ./validate/run_minimal.sh > "var/reports/native_run_minimal_${TS}.out" 2>&1
  run_rc=$?
  ./validate/generate_evidence.sh
  ev_rc=$?
  set -e
else
  echo "[native-check] gate FAILED — not executing run steps"
fi

# Receipt
{
  echo "{"
  echo "  \"timestamp\": \"${TS}\","
  echo "  \"host\": \"${HOST}\","
  echo "  \"distro\": \"${DISTRO}\","
  echo "  \"kernel\": \"${KREL}\","
  echo "  \"is_wsl\": ${IS_WSL},"
  echo "  \"gpu_info\": \"${GPU_INFO}\","
  echo "  \"gate\": { \"passed\": ${ok_gate}, \"reason\": \"${reason}\" },"
  echo "  \"steps\": { \"install_rc\": ${install_rc}, \"run_minimal_rc\": ${run_rc}, \"evidence_rc\": ${ev_rc} }"
  echo "}"
} > "$RECEIPT"

echo "[native-check] receipt -> $RECEIPT"
[[ $ok_gate -eq 1 ]] || exit 42
exit 0
