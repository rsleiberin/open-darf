#!/usr/bin/env bash
set -euo pipefail
SPLIT="${1:-dev}"
MODEL="${NER_MODEL_DIR:-$HOME/.darf/models/biobert_ner}"
INP="var/datasets/normalized/biored_concept/${SPLIT}.jsonl"
OUT="var/receipts/phase6c/entities"
python -m scripts.relation_extraction.ner_infer --model "$MODEL" --input "$INP" --out_dir "$OUT" --split "$SPLIT"
