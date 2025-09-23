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
  echo "  \"kernel\": \"$(uname -sr)\","
  echo "  \"distro\": \"$( (lsb_release -ds 2>/dev/null || grep -m1 PRETTY_NAME /etc/os-release | cut -d= -f2 | tr -d '\"') )\","
  echo "  \"python\": \"$(python3 -V 2>/dev/null || echo none)\","
  echo "  \"nvcc\": \"$(nvcc --version 2>/dev/null | tr '\n' ' ' || echo none)\","
  echo "  \"nvidia_smi\": \"$(nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv,noheader 2>/dev/null | tr '\n' ';' || echo none)\""
  echo "}"
} > "${TMP}/system_snapshot.json"

echo "[evidence] probing torch/cuda…"
python3 - << 'PY' > "${TMP}/torch_probe.json" || true
import json
info={"ok": False, "cuda_available": None, "devices": []}
try:
    import torch
    info["cuda_available"]=torch.cuda.is_available()
    if info["cuda_available"]:
        for i in range(torch.cuda.device_count()):
            p=torch.cuda.get_device_properties(i)
            info["devices"].append({"index": i, "name": p.name, "total_memory": int(getattr(p,"total_memory",0))})
    info["ok"]=True
except Exception as e:
    info["error"]=str(e)
print(json.dumps(info))
PY

echo "[evidence] timing probe…"
python3 - << 'PY' > "${TMP}/timing_probe.json" || true
import json, time, statistics
def microbench(n_outer=10, n_inner=10000):
    mins=[]
    for _ in range(n_outer):
        best=1e9
        for _ in range(n_inner):
            t0=time.perf_counter(); t1=time.perf_counter()
            d=t1-t0
            if d<best: best=d
        mins.append(best)
    return {"min_delta_s": min(mins), "median_min_delta_s": statistics.median(mins), "samples": len(mins), "inner_iters": n_inner}
info=time.get_clock_info("perf_counter")
mb=microbench()
print(json.dumps({
  "clock":{"resolution_s": info.resolution, "monotonic": info.monotonic, "adjustable": info.adjustable},
  "microbench": mb,
  "sub_ms_supported": mb["min_delta_s"] < 1e-3
}))
PY

# Run minimal validator if present
REL_RUN_MIN="$REL_RUN_MIN"
if [[ -x "$REL_RUN_MIN" ]]; then
  echo "[evidence] running $REL_RUN_MIN …"
  set +e
  "$REL_RUN_MIN" > "${TMP}/run_minimal_stdout.txt" 2> "${TMP}/run_minimal_stderr.txt"
  echo $? > "${TMP}/run_minimal_exitcode.txt"
  set -e
else
  echo "[note] $REL_RUN_MIN not found; skipping minimal run." | tee "${TMP}/note_missing_run_minimal.txt"
fi

# Include git context
git rev-parse HEAD > "${TMP}/git_head.txt" || true
git status --porcelain=v1 > "${TMP}/git_status.txt" || true

# Package evidence
tar -czf "$OUT" -C "$TMP" .
echo "[evidence] packaged -> $OUT"
