#!/bin/bash
set -euo pipefail
printf "===\n===\n===\n"
echo "=== DARF Phase 7O — SciERC Full Evaluation (GPU) ==="
# Usage: bash scripts/phase7o/run_scierc_full.sh

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PYTORCH_IMAGE="pytorch/pytorch:2.1.2-cuda12.1-cudnn8-runtime"
RECEIPTS_DIR="${HOME}/darf_receipts"
TIMESTAMP="$(date +'%Y%m%d_%H%M%S')"
RECEIPT="${RECEIPTS_DIR}/scierc_full_${TIMESTAMP}.log"
mkdir -p "${RECEIPTS_DIR}"

DOCKER_FLAGS=(--rm --gpus all --ipc=host)
DOCKER_FLAGS+=( -e NVIDIA_VISIBLE_DEVICES=all -e NVIDIA_DRIVER_CAPABILITIES=compute,utility )
DOCKER_FLAGS+=( -e LD_PRELOAD= -e LD_LIBRARY_PATH= )
DOCKER_FLAGS+=( -v "${PROJECT_ROOT}":/app -w /app )
DOCKER_FLAGS+=( -v "${HOME}/.cache/huggingface":/root/.cache/huggingface )

select_entrypoint () {
  python - << 'PY'
import os, sys, re, json, subprocess, shlex, pathlib
ROOT = pathlib.Path("external/PURE/code")
cands = [
  "run_scierc_eval.py","eval_scierc.py","train_scierc.py",
  "evaluate.py","main.py","runner.py"
]
files = []
if ROOT.exists():
  for p in ROOT.rglob("*.py"):
    files.append(str(p))
else:
  files = []

# Prefer files whose names mention 'scierc'
pref = [f for f in files if re.search(r'scierc', os.path.basename(f), re.I)]
if not pref:
  pref = files

# Probe with "-h" to see if they expose usage without running heavy work
def has_help(f):
  try:
    cmd = f"python {shlex.quote(f)} -h"
    p = subprocess.run(cmd, shell=True, capture_output=True, text=True, cwd=".")
    out = p.stdout + "\n" + p.stderr
    if p.returncode == 0 or re.search(r'usage:|--help', out, re.I):
      return True
  except Exception:
    pass
  return False

ok = [f for f in pref if has_help(f)]
# Heuristics: prefer *_eval.py
for f in ok:
  if re.search(r'_eval\.py$', f): 
    print(f); sys.exit(0)
# else first OK
print(ok[0] if ok else "")
PY
}

ENTRYPOINT="$(select_entrypoint)"

if [ -z "${ENTRYPOINT}" ]; then
  echo "[FATAL] No SciERC entrypoint discovered under external/PURE/code (help-ok set empty)."
  exit 4
fi

echo "[run] ENTRYPOINT=${ENTRYPOINT}"
echo "[run] Receipt: ${RECEIPT}"

# Base deps
docker run "${DOCKER_FLAGS[@]}" "${PYTORCH_IMAGE}" bash -s << 'IN_CONTAINER' | tee -a "${RECEIPT}"
set -euo pipefail
python -m pip -q install --upgrade pip setuptools wheel
python -m pip -q install --no-cache-dir transformers==4.31.0 datasets==2.14.0 scikit-learn==1.3.0
IN_CONTAINER

# Try project requirements if present
REQS=""
for C in external/PURE/requirements.txt external/PURE/requirements-min.txt external/PURE/reqs.txt ; do
  [ -f "$C" ] && REQS="$C" && break
done
if [ -n "${REQS}" ]; then
  docker run "${DOCKER_FLAGS[@]}" "${PYTORCH_IMAGE}" bash -lc "python -m pip install --no-cache-dir -r ${REQS}" | tee -a "${RECEIPT}"
fi

# Run evaluation with GPU; arguments are best-effort. Adjust if script prints usage.
set +e
docker run "${DOCKER_FLAGS[@]}" "${PYTORCH_IMAGE}" bash -lc \
  "/usr/bin/time -p python ${ENTRYPOINT} --device cuda --dataset scierc --eval --batch 16 --epochs 1" \
  | tee -a "${RECEIPT}"
RC=${PIPESTATUS[0]}
set -e

# Parse an F1 candidate if printed
F1=$(grep -Eo 'F1(_micro)?[:=][[:space:]]*[0-9.]+%?' "${RECEIPT}" | head -n1 | sed -E 's/.*[:=][[:space:]]*//')
echo "[parse] F1_micro_candidate=${F1}" | tee -a "${RECEIPT}"

echo "=== SciERC full evaluation finished (rc=${RC}). Receipt: ${RECEIPT} ==="
exit "${RC}"
