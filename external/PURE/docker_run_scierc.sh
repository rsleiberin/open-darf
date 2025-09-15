#!/usr/bin/env bash
set -euo pipefail
DATA_DIR="${1:-/data}"
OUT_DIR="${2:-/out}"
SPLIT="${SPLIT:-test}"

echo "[EP] Starting docker_run_scierc.sh (DATA_DIR=${DATA_DIR}, OUT_DIR=${OUT_DIR}, SPLIT=${SPLIT})"

# Install runtime deps compatible with PURE legacy stack (Python 3.7)
python - <<'PY'
import sys, subprocess
def pipi(*pkgs): 
    subprocess.check_call([sys.executable, "-m", "pip", "install", "-q"] + list(pkgs))
# Minimal, pinned set for PURE (cpu torch already baked in image)
pipi("tqdm==4.67.1")
pipi("numpy<1.22")
pipi("overrides==3.1.0", "requests==2.25.1", "transformers==3.0.2")
# AllenNLP 0.9 pulls spacy<2.2; allow it to resolve
pipi("allennlp==0.9.0")
print("[EP] Runtime deps installed.")
PY

# Run PURE entity script; PURE repo is copied at /app in image
cd /app
if [ ! -f run_entity.py ]; then
  echo "[EP] ERROR: /app/run_entity.py not found." >&2
  exit 3
fi

mkdir -p "${OUT_DIR}"
echo "[EP] Executing PURE entity run..."
# NOTE: PURE CLI varies by recipe; we use the entity entry for SciERC-style predict.
# If PURE expects config files, adjust here; harness only needs a JSONL of predictions.
python run_entity.py \
  --dataset "${DATA_DIR}" \
  --split "${SPLIT}" \
  --output "${OUT_DIR}/predictions.json" || {
    echo "[EP] WARN: PURE run_entity.py returned non-zero; attempting to capture logs only."
    exit 1
}

# Normalize to JSONL if evaluator expects it
python - <<'PY'
import json, sys, pathlib
out_dir = pathlib.Path("/out")
src = out_dir/"predictions.json"
dst = out_dir/"preds.jsonl"
if src.exists():
    try:
        data = json.load(open(src))
        with open(dst, "w") as w:
            if isinstance(data, list):
                for r in data: w.write(json.dumps(r)+"\n")
            elif isinstance(data, dict):
                for k,v in data.items(): w.write(json.dumps({k:v})+"\n")
            else:
                w.write(json.dumps({"pred": data})+"\n")
        print("[EP] Wrote", dst)
    except Exception as e:
        print("[EP] WARN: could not normalize predictions:", e)
else:
    print("[EP] WARN: predictions.json missing; skipping normalization.")
PY

echo "[EP] Done."
