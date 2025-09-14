#!/usr/bin/env bash
set -euo pipefail

echo "[gpu_diag] BEGIN"
overall_rc=0

# Basic system context
echo "[gpu_diag] uname: $(uname -a)"
if command -v lsb_release >/dev/null 2>&1; then
  echo "[gpu_diag] distro: $(lsb_release -ds || true)"
fi
echo "[gpu_diag] kernel: $(uname -r)"

# nvidia-smi presence & data
if command -v nvidia-smi >/dev/null 2>&1; then
  echo "[gpu_diag] nvidia-smi found"
  if nvidia-smi -L 2>/dev/null; then
    :
  else
    echo "[gpu_diag] warning: nvidia-smi -L returned non-zero" >&2
    overall_rc=1
  fi

  # Compact CSV of key properties
  if nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv,noheader 2>/dev/null; then
    :
  else
    echo "[gpu_diag] warning: nvidia-smi --query-gpu failed" >&2
    overall_rc=1
  fi
else
  echo "[gpu_diag] nvidia-smi NOT found"
  overall_rc=2
fi

# Device nodes
if ls /dev/nvidia* >/dev/null 2>&1; then
  echo "[gpu_diag] /dev/nvidia* present:"
  ls -l /dev/nvidia* || true
else
  echo "[gpu_diag] /dev/nvidia* not present"
  overall_rc=$(( overall_rc == 0 ? 3 : overall_rc ))
fi

# Driver module info (best-effort)
if command -v modinfo >/dev/null 2>&1; then
  if modinfo nvidia >/dev/null 2>&1; then
    echo "[gpu_diag] modinfo nvidia: OK"
    modinfo nvidia | head -n 20 || true
  else
    echo "[gpu_diag] modinfo nvidia: module not loaded" >&2
  fi
fi

# CUDA libraries on linker path
if command -v ldconfig >/dev/null 2>&1; then
  echo "[gpu_diag] ldconfig check for CUDA libs:"
  ldconfig -p | grep -E 'libcuda|libcudart|cudnn' || echo "[gpu_diag] (none found on ldconfig cache)"
fi

echo "[gpu_diag] END rc=${overall_rc}"
exit "${overall_rc}"
