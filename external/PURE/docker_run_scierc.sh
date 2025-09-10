#!/usr/bin/env bash
set -Eeuo pipefail
DATA_DIR="/data"
OUT_DIR="/out"

while [ $# -gt 0 ]; do
  case "$1" in
    --data_dir) DATA_DIR="$2"; shift 2 ;;
    --out_dir)  OUT_DIR="$2"; shift 2 ;;
    *) shift ;;
  esac
done

ENT_DIR="/app/scierc_models/ent-scib-ctx0"
REL_DIR="/app/scierc_models/rel-scib-ctx0"

python run_entity.py \
  --do_eval --eval_test \
  --context_window 0 \
  --task scierc \
  --data_dir "${DATA_DIR}" \
  --model allenai/scibert_scivocab_uncased \
  --output_dir "${ENT_DIR}"

python run_relation.py \
  --task scierc \
  --do_eval --eval_test \
  --model allenai/scibert_scivocab_uncased \
  --do_lower_case \
  --context_window 0 \
  --max_seq_length 128 \
  --entity_output_dir "${ENT_DIR}" \
  --output_dir "${REL_DIR}"

mkdir -p "${OUT_DIR}"
cp -f "${REL_DIR}/predictions.json" "${OUT_DIR}/predictions.json"
echo "[PURE-Docker] predictions exported to ${OUT_DIR}/predictions.json"
