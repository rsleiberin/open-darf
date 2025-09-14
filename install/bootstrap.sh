#!/usr/bin/env bash
set -euo pipefail

echo "==="
echo "==="
echo "==="

echo "[M1] BEGIN bootstrap (native Ubuntu)"
TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUTDIR="var/receipts/${TS}_bootstrap"
mkdir -p "${OUTDIR}"

rc=0

# Detect OS and WSL
OSREL="$( (lsb_release -ds 2>/dev/null || grep PRETTY_NAME= /etc/os-release | cut -d= -f2 | tr -d '"') || echo unknown )"
KREL="$(uname -r)"
OSREL_LC="$(printf "%s" "$OSREL" | tr '[:upper:]' '[:lower:]')"
KREL_LC="$(printf "%s" "$KREL" | tr '[:upper:]' '[:lower:]')"

echo "[info] OS: ${OSREL}" | tee "${OUTDIR}/os.out"
echo "[info] Kernel: ${KREL}" | tee -a "${OUTDIR}/os.out"

WSL=0
if printf "%s" "$KREL_LC" | grep -qi "wsl"; then WSL=1; fi
if [ -e /proc/sys/kernel/osrelease ] && grep -qi "wsl" /proc/sys/kernel/osrelease; then WSL=1; fi
if [ -e /run/WSL ]; then WSL=1; fi

if [ "$WSL" -eq 1 ]; then
  echo "[gate] WSL detected; Phase 7R targets native Ubuntu (bare-metal or GPU-passthrough VM)."
  echo "[gate] Action: install/run on Ubuntu 22.04 LTS (preferred) or 20.04 LTS with NVIDIA driver R535+."
  echo "41" > "${OUTDIR}/bootstrap.rc"
  echo "[M1] END bootstrap rc=41 (WSL gated)"
  exit 41
fi

# Secure Boot state (best-effort)
echo "[info] Secure Boot state:"
(mokutil --sb-state 2>/dev/null || echo "(mokutil not available)") | tee "${OUTDIR}/secureboot.out" || true

# Ensure ubuntu-drivers exists
if ! command -v ubuntu-drivers >/dev/null 2>&1; then
  echo "[fatal] 'ubuntu-drivers' not found. Install ubuntu-drivers-common: sudo apt-get update && sudo apt-get install -y ubuntu-drivers-common"
  echo "12" > "${OUTDIR}/bootstrap.rc"
  echo "[M1] END bootstrap rc=12"
  exit 12
fi

# Driver install (idempotent)
echo "[step] Installing NVIDIA driver via 'ubuntu-drivers autoinstall' (may require reboot)"
if sudo ubuntu-drivers autoinstall; then
  echo "[ok] Driver install command completed"
else
  echo "[warn] ubuntu-drivers autoinstall returned non-zero; capturing apt policy"
  (apt-cache policy | sed -n "1,120p") > "${OUTDIR}/apt_policy.out" || true
  rc=20
fi

# Post-checks
echo "[post] nvidia-smi:"
if nvidia-smi >/dev/null 2>&1; then
  echo "[ok] nvidia-smi available" | tee -a "${OUTDIR}/gpu_bootstrap.out"
else
  echo "[fail] nvidia-smi unavailable — a reboot is typically required after driver install." | tee -a "${OUTDIR}/gpu_bootstrap.out"
  rc="${rc:-0}"; rc=$(( rc == 0 ? 21 : rc ))
fi

# libcuda probe
python3 - << 'PY' | tee -a "${OUTDIR}/gpu_bootstrap.out"
import ctypes, sys
try:
    ctypes.CDLL("libcuda.so.1")
    print("[ok] libcuda.so.1 loadable")
except Exception as e:
    print(f"[fail] libcuda.so.1 load failed: {e}")
    sys.exit(1)
PY
ld_rc=$?
if [ "$ld_rc" -ne 0 ]; then
  rc="${rc:-0}"; rc=$(( rc == 0 ? 22 : rc ))
fi

echo "${rc:-0}" > "${OUTDIR}/bootstrap.rc"
echo "[M1] END bootstrap rc=$(cat "${OUTDIR}/bootstrap.rc")"
exit "${rc:-0}"
