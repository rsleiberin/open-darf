#!/usr/bin/env bash
set -euo pipefail
echo "[doctor] system snapshot"
uname -sr
python3 -V || true
nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv,noheader 2>/dev/null || true
echo "[doctor] done"
