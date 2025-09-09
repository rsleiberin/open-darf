#!/usr/bin/env bash
set -euo pipefail
MET="${1:?metrics.json path required}"
LAT_START="${2:-}"
LAT_END="${3:-}"

# Compute latency in ms if both stamps provided
LAT_MS="0"
if [ -n "$LAT_START" ] && [ -n "$LAT_END" ]; then
  # stamps are expected as epoch-ms integers
  if [[ "$LAT_START" =~ ^[0-9]+$ ]] && [[ "$LAT_END" =~ ^[0-9]+$ ]]; then
    LAT_MS="$(( LAT_END - LAT_START ))"
    [ "$LAT_MS" -lt 0 ] && LAT_MS="0"
  fi
fi

# GPU memory snapshot (used or total-best-effort)
GPU_MB="0"
if command -v nvidia-smi >/dev/null 2>&1; then
  GPU_MB="$(nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits 2>/dev/null | head -n1 | tr -d '[:space:]' || echo 0)"
  [[ "$GPU_MB" =~ ^[0-9]+$ ]] || GPU_MB="0"
fi

python3 - "$MET" "$LAT_MS" "$GPU_MB" << 'PY'
import json, sys, pathlib
met = pathlib.Path(sys.argv[1])
lat = float(sys.argv[2])
gpu = float(sys.argv[3])
try:
    data = json.loads(met.read_text(encoding="utf-8"))
except Exception:
    data = {}
data["latency_ms"] = data.get("latency_ms", 0.0) if lat == 0 else lat
data["gpu_mem_mb"] = data.get("gpu_mem_mb", 0.0) if gpu == 0 else gpu
met.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
PY
echo "[PERF] Updated $MET with latency_ms=$LAT_MS gpu_mem_mb=$GPU_MB"
