#!/usr/bin/env bash
set -euo pipefail

echo "==="
echo "==="
echo "==="

echo "[M2] BEGIN python/cuda (venv + Torch cu12x)"

TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUTDIR="var/receipts/${TS}_python_cuda"
mkdir -p "${OUTDIR}"

# Detect WSL (Phase 7R requires native Ubuntu)
KREL_LC="$(uname -r | tr '[:upper:]' '[:lower:]')"
WSL=0
if printf "%s" "$KREL_LC" | grep -qi "wsl"; then WSL=1; fi
if [ -e /proc/sys/kernel/osrelease ] && grep -qi "wsl" /proc/sys/kernel/osrelease; then WSL=1; fi
if [ -e /run/WSL ]; then WSL=1; fi

if [ "$WSL" -eq 1 ]; then
  echo "[gate] WSL detected; skipping Torch CUDA install to avoid heavy downloads without GPU device nodes."
  echo "41" > "${OUTDIR}/python_cuda.rc"
  echo "[M2] END python/cuda rc=41 (WSL gated)"
  exit 41
fi

RC=0

PYBIN="$(command -v python3 || true)"
if [ -z "${PYBIN}" ]; then
  echo "[fatal] python3 not found" | tee "${OUTDIR}/pip_env.out"
  echo "12" > "${OUTDIR}/python_cuda.rc"
  echo "[M2] END python/cuda rc=12"
  exit 12
fi

VENVDIR="${HOME}/.local/share/open-darf/venv"
if [ ! -d "${VENVDIR}" ]; then
  python3 -m venv "${VENVDIR}"
fi
# shellcheck disable=SC1090
. "${VENVDIR}/bin/activate"
python -m pip install --upgrade pip wheel setuptools | tee "${OUTDIR}/pip_upgrade.out"

# Prefer official cu12x wheels (allow override via TORCH_INDEX_URL)
TORCH_IDX="${TORCH_INDEX_URL:-https://download.pytorch.org/whl/cu126}"
echo "[info] Installing Torch stack from ${TORCH_IDX}" | tee -a "${OUTDIR}/pip_env.out"
python - << 'PY' 2>&1 | tee -a "${OUTDIR}/pip_env.out"
import sys, subprocess, os
idx=os.environ.get("TORCH_IDX","https://download.pytorch.org/whl/cu126")
pkgs=["torch","torchvision","torchaudio","numpy"]
subprocess.check_call([sys.executable,"-m","pip","install","--index-url",idx,*pkgs])
PY

# Torch diagnostic
python tools/torch_diag.py | tee "${OUTDIR}/torch_diag.out"
RC="${PIPESTATUS[0]}"

echo "${RC}" > "${OUTDIR}/python_cuda.rc"
echo "[M2] END python/cuda rc=${RC}"
exit "${RC}"
