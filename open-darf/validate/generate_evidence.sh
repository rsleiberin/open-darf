#!/usr/bin/env bash
set -euo pipefail

TS="$(date -u +%Y%m%dT%H%M%SZ)"
HOST="$(hostname)"
OUT="open-darf-report-${HOST}-${TS}.tar.gz"
TMP="var/reports/_evidence_${TS}"
mkdir -p "$TMP"

echo "[evidence] collecting system snapshot…"
{
  echo "{"
  echo "  \"timestamp\": \"${TS}\","
  echo "  \"host\": \"${HOST}\","
  echo "  \"kernel\": \"$(uname -sr)\" ,"
  echo "  \"distro\": \"$( (lsb_release -ds 2>/dev/null || cat /etc/os-release | grep PRETTY_NAME | cut -d= -f2 | tr -d '\"') )\","
  echo "  \"python\": \"$(python3 -V 2>/dev/null || echo none)\","
  echo "  \"nvcc\": \"$(nvcc --version 2>/dev/null | tr '\n' ' ' || echo none)\","
  echo "  \"nvidia_smi\": \"$(nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv,noheader 2>/dev/null | tr '\n' ';' || echo none)\""
  echo "}"
} > "${TMP}/system_snapshot.json"

echo "[evidence] probing torch/cuda…"
python3 - << 'PY' > "${TMP}/torch_probe.json" || true
import json, sys
info = {"ok": False, "cuda_available": None, "devices": []}
try:
    import torch
    info["cuda_available"] = torch.cuda.is_available()
    if info["cuda_available"]:
        for i in range(torch.cuda.device_count()):
            props = torch.cuda.get_device_properties(i)
            info["devices"].append({
                "index": i,
                "name": props.name,
                "total_memory": props.total_memory
            })
    info["ok"] = True
except Exception as e:
    info["error"] = str(e)
print(json.dumps(info))
PY

# Run minimal validator if present (non-fatal on failure; we’re packaging evidence)
if [[ -x "./validate/run_minimal.sh" ]]; then
  echo "[evidence] running validate/run_minimal.sh…"
  set +e
  ./validate/run_minimal.sh > "${TMP}/run_minimal_stdout.txt" 2> "${TMP}/run_minimal_stderr.txt"
  echo $? > "${TMP}/run_minimal_exitcode.txt"
  set -e
else
  echo "[note] ./validate/run_minimal.sh not found; skipping pipeline run." | tee "${TMP}/note_missing_run_minimal.txt"
fi

# Include recent git status and head
git rev-parse HEAD > "${TMP}/git_head.txt"
git status --porcelain=v1 > "${TMP}/git_status.txt"

# Package
tar -czf "$OUT" -C "$TMP" .
echo "[evidence] packaged -> $OUT"
