#!/usr/bin/env bash
set -euo pipefail

echo "==="
echo "==="
echo "==="

echo "[M2] BEGIN python/cuda (venv + Torch cu12x with preflight net probes)"

TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUTDIR="var/receipts/${TS}_python_cuda"
mkdir -p "${OUTDIR}"

# WSL gate (Phase 7R requires native)
KREL_LC="$(uname -r | tr '[:upper:]' '[:lower:]')"
WSL=0
printf "%s" "$KREL_LC" | grep -qi "wsl" && WSL=1
[ -e /proc/sys/kernel/osrelease ] && grep -qi "wsl" /proc/sys/kernel/osrelease && WSL=1
[ -e /run/WSL ] && WSL=1
if [ "$WSL" -eq 1 ]; then
  echo "[gate] WSL detected; skipping Torch CUDA install." | tee -a "${OUTDIR}/python_cuda.out"
  echo "41" > "${OUTDIR}/python_cuda.rc"
  echo "[M2] END rc=41 (WSL gated)"
  exit 41
fi

# Connectivity probes (always before large wheel downloads)
if [ -x tools/net_probe.sh ]; then
  echo "[preflight] Running net probes…" | tee -a "${OUTDIR}/python_cuda.out"
  tools/net_probe.sh | tee "${OUTDIR}/net_probe.inline.out" || true
fi

# Python + venv
PYBIN="$(command -v python3 || true)"
if [ -z "${PYBIN}" ]; then
  echo "[fatal] python3 not found" | tee -a "${OUTDIR}/python_cuda.out"
  echo "12" > "${OUTDIR}/python_cuda.rc"; echo "[M2] END rc=12"; exit 12
fi
VENVDIR="${HOME}/.local/share/open-darf/venv"
[ -d "${VENVDIR}" ] || python3 -m venv "${VENVDIR}"
# shellcheck disable=SC1090
. "${VENVDIR}/bin/activate"

python -m pip install --upgrade pip wheel setuptools | tee "${OUTDIR}/pip_upgrade.out"

TORCH_INDEX_URL="${TORCH_INDEX_URL:-https://download.pytorch.org/whl/cu126}"
echo "[pip] Installing torch/vision/audio from ${TORCH_INDEX_URL}" | tee -a "${OUTDIR}/python_cuda.out"
set +e
python - << 'PY' 2>&1 | tee -a "${OUTDIR}/pip_install.out"
import os, sys, subprocess
idx=os.environ.get("TORCH_INDEX_URL","https://download.pytorch.org/whl/cu126")
pkgs=["torch","torchvision","torchaudio","numpy"]
subprocess.check_call([sys.executable,"-m","pip","install","--index-url",idx,*pkgs])
PY
PIP_RC=${PIPESTATUS[0]}
set -e

# Probe torch
python tools/torch_diag.py | tee "${OUTDIR}/torch_diag.out"
TD_RC="${PIPESTATUS[0]}"

# Overall RC
RC="$(( PIP_RC != 0 ? PIP_RC : TD_RC ))"
echo "${RC}" > "${OUTDIR}/python_cuda.rc"
echo "[M2] END python/cuda rc=${RC}"
exit "${RC}"
