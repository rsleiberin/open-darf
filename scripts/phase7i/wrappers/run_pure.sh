#!/usr/bin/env bash
# PURE wrapper: dockerized (py3.7 bullseye) preferred; ensure tqdm + numpy at runtime.
set -Eeuo pipefail
if [ -z "${BASH_VERSION:-}" ]; then exec /usr/bin/env bash "$0" "$@"; fi

DATA_PATH=""; SPLIT=""; OUTDIR=""
while [ $# -gt 0 ]; do
  case "$1" in
    --data|--dataset) DATA_PATH="$2"; shift 2 ;;
    --split) SPLIT="$2"; shift 2 ;;
    --outdir) OUTDIR="$2"; shift 2 ;;
    --) shift; break ;;
    *) shift ;;
  esac
done
OUTDIR="${OUTDIR:-${PWD}/out}"
mkdir -p "${OUTDIR}"

DS_ROOT="${HOME}/darf-source"
SCIERC_DATA="${DATA_PATH:-${DS_ROOT}/data/scierc}"
PRED_JSONL="${OUTDIR}/preds.jsonl"

if command -v docker >/dev/null 2>&1; then
  IMAGE_TAG="darf/pure:py37-bullseye"
  TMP_OUT="$(mktemp -d)"

  docker run --rm \
    --entrypoint bash \
    -v "${SCIERC_DATA}:/data:ro" \
    -v "${TMP_OUT}:/out" \
    -w /app \
    "${IMAGE_TAG}" -lc '
      set -Eeuo pipefail
      # Ensure tqdm and numpy (<=1.21.x for Py3.7)
      python - <<PY || python -m pip install --no-cache-dir tqdm && echo "[PURE] Installed tqdm at runtime"
try:
  import tqdm  # noqa
  print("[PURE] tqdm present")
except Exception:
  raise SystemExit(1)
PY
      python - <<PY || python -m pip install --no-cache-dir "numpy<1.22" && echo "[PURE] Installed numpy<1.22 at runtime"
try:
  import numpy as np  # noqa
  print("[PURE] numpy present")
except Exception:
  raise SystemExit(1)
PY
      python run_entity.py \
        --do_eval --eval_test \
        --context_window 0 \
        --task scierc \
        --data_dir /data \
        --model allenai/scibert_scivocab_uncased \
        --output_dir /app/scierc_models/ent-scib-ctx0
      python run_relation.py \
        --task scierc \
        --do_eval --eval_test \
        --model allenai/scibert_scivocab_uncased \
        --do_lower_case \
        --context_window 0 \
        --max_seq_length 128 \
        --entity_output_dir /app/scierc_models/ent-scib-ctx0 \
        --output_dir /app/scierc_models/rel-scib-ctx0
      cp -f /app/scierc_models/rel-scib-ctx0/predictions.json /out/predictions.json
    '

  if [ ! -s "${TMP_OUT}/predictions.json" ]; then
    echo "[PURE] ERROR: predictions.json missing from docker run." >&2
    exit 7
  fi

  python3 - <<PY
import json, sys
src = "${TMP_OUT}/predictions.json"; dst = "${PRED_JSONL}"
with open(src) as f: data = json.load(f)
with open(dst,"w") as w:
    if isinstance(data,list):
        for r in data: w.write(json.dumps(r)+"\n")
    elif isinstance(data,dict):
        for k,v in data.items(): w.write(json.dumps({k:v})+"\n")
    else:
        w.write(json.dumps({"pred": data})+"\n")
print(f"[PURE] Wrote {dst}")
PY
  echo "[PURE] Done (docker)."
  exit 0
fi

# Fallback to local venv if docker missing
PURE_DIR="${DS_ROOT}/external/PURE"
PURE_VENV="${PURE_DIR}/.venv"
if [ -x "${PURE_VENV}/bin/python" ]; then
  ENT_DIR="${PURE_DIR}/scierc_models/ent-scib-ctx0"
  REL_DIR="${PURE_DIR}/scierc_models/rel-scib-ctx0"
  "${PURE_VENV}/bin/python" "${PURE_DIR}/run_entity.py" \
    --do_eval --eval_test --context_window 0 --task scierc \
    --data_dir "${SCIERC_DATA}" \
    --model allenai/scibert_scivocab_uncased \
    --output_dir "${ENT_DIR}"
  "${PURE_VENV}/bin/python" "${PURE_DIR}/run_relation.py" \
    --task scierc --do_eval --eval_test \
    --model allenai/scibert_scivocab_uncased --do_lower_case \
    --context_window 0 --max_seq_length 128 \
    --entity_output_dir "${ENT_DIR}" --output_dir "${REL_DIR}"
  PRED_JSON="${REL_DIR}/predictions.json"
  python3 - <<PY
import json, sys
src="${PRED_JSON}"; dst="${PRED_JSONL}"
data=json.load(open(src))
with open(dst,"w") as w:
    if isinstance(data,list):
        for r in data: w.write(json.dumps(r)+"\n")
    elif isinstance(data,dict):
        for k,v in data.items(): w.write(json.dumps({k:v})+"\n")
    else:
        w.write(json.dumps({"pred": data})+"\n")
print(f"[PURE] Wrote {dst}")
PY
  echo "[PURE] Done (venv)."
  exit 0
fi

echo "[PURE] ERROR: Neither docker nor local venv available to run PURE." >&2
exit 8
