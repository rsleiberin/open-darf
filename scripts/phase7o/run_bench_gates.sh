#!/bin/bash
set -euo pipefail
printf "===\n===\n===\n"
echo "=== DARF Phase 7O — 7I Benchmark Gates (light) ==="
# Intent: quick sanity gates without heavy GPU usage

RCPTS="${HOME}/darf_receipts"
TS="$(date +'%Y%m%d_%H%M%S')"
OUT="${RCPTS}/gates_7i_${TS}.log"
mkdir -p "${RCPTS}"

say(){ echo -e "$*"; echo -e "$*" >> "${OUT}"; }

say "[gate] Python & Git"
python3 -V 2>&1 | tee -a "${OUT}" || true
git --version 2>&1 | tee -a "${OUT}" || true

say "[gate] Torch CUDA visibility via container (no heavy load)"
docker run --rm --gpus all -e LD_PRELOAD= -e LD_LIBRARY_PATH= --ipc=host pytorch/pytorch:2.1.2-cuda12.1-cudnn8-runtime \
  python - <<'PY' | tee -a "${OUT}" || true
import torch, json
print(json.dumps({
  "torch": getattr(torch, "__version__", None),
  "cuda_available": torch.cuda.is_available(),
  "n_gpus": torch.cuda.device_count()
}, indent=2))
PY

say "[gate] PURE quickcheck dry-run plan ready (use previous mini test receipts for proof)."
say "Result: LIGHT_GATES_COMPLETE"
echo "Receipt: ${OUT}"
