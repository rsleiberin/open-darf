#!/usr/bin/env bash
set -euo pipefail

echo "[wsl_gate] BEGIN"
RC=41
TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUTDIR="var/receipts/${TS}_wsl_gate"
mkdir -p "$OUTDIR"

# Evidence
UNAME="$(uname -a || true)"
OSREL="$(lsb_release -ds 2>/dev/null || echo N/A)"
KREL="$(uname -r || true)"
WSL_HINTS=0
[[ "${KREL,,}" == *wsl* ]] && WSL_HINTS=1
grep -qi wsl /proc/sys/kernel/osrelease 2>/dev/null && WSL_HINTS=1
[ -e /run/WSL ] && WSL_HINTS=1

echo "[evidence] uname -a: $UNAME" | tee "$OUTDIR/wsl_gate.out"
echo "[evidence] lsb_release: $OSREL" | tee -a "$OUTDIR/wsl_gate.out"
echo "[evidence] kernel: $KREL" | tee -a "$OUTDIR/wsl_gate.out"
echo "[evidence] /run/WSL present: $([ -e /run/WSL ] && echo yes || echo no)" | tee -a "$OUTDIR/wsl_gate.out"

# GPU signals
if command -v nvidia-smi >/dev/null 2>&1; then
  echo "[gpu] nvidia-smi -L:" | tee -a "$OUTDIR/wsl_gate.out"
  nvidia-smi -L 2>&1 | tee -a "$OUTDIR/wsl_gate.out" || true
  if ls /dev/nvidia* >/dev/null 2>&1; then
    echo "[gpu] /dev/nvidia* present" | tee -a "$OUTDIR/wsl_gate.out"
  else
    echo "[gpu] /dev/nvidia* NOT present (typical under WSL CUDA path)" | tee -a "$OUTDIR/wsl_gate.out"
  fi
else
  echo "[gpu] nvidia-smi not found" | tee -a "$OUTDIR/wsl_gate.out"
fi

# Linker libs
if command -v ldconfig >/dev/null 2>&1; then
  echo "[libs] ldconfig CUDA entries:" | tee -a "$OUTDIR/wsl_gate.out"
  (ldconfig -p | grep -E 'libcuda|libcudart|cudnn' || true) | tee -a "$OUTDIR/wsl_gate.out"
fi

# Why we gate
cat << 'WHY' | tee -a "$OUTDIR/wsl_gate.out" >/dev/null
[why]
- Phase 7R requires *native* Ubuntu with kernel NVIDIA modules loaded.
- Under WSL2, CUDA is proxied via /usr/lib/wsl, and device nodes (/dev/nvidia*) are absent.
- Our validator and timing receipts must run on real device nodes for grant-grade evidence.
[action]
- Boot native Ubuntu 22.04 LTS (preferred) or 20.04 LTS on bare-metal (or a VM with proper GPU passthrough).
- Then run: ./install.sh  → this will install drivers, Torch CUDA, and execute the validator.
WHY

echo "${RC}" > "$OUTDIR/wsl_gate.rc"
echo "[wsl_gate] END rc=${RC}"
exit "${RC}"
