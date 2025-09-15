#!/usr/bin/env bash
set -euo pipefail
# Args: ROOT OUTDIR DATASET SPLIT MODEL MET GPU_MB
ROOT="$1"; OUTDIR="$2"; DATASET="$3"; SPLIT="$4"; MODEL="$5"; MET="$6"; GPU_MB="${7:-0}"

# Prefer filtered preds if present
SRC_PREDS="$OUTDIR/preds.filtered.json"
[ -s "$SRC_PREDS" ] || SRC_PREDS="$OUTDIR/preds.json"

GOLD_JSON=""
if [ "$DATASET" = "scierc" ]; then
  [ -f "$ROOT/data/scierc/$SPLIT.jsonl" ] && GOLD_JSON="$ROOT/data/scierc/$SPLIT.jsonl" || true
  [ -z "$GOLD_JSON" ] && [ -f "$ROOT/data/scierc/$SPLIT.json" ] && GOLD_JSON="$ROOT/data/scierc/$SPLIT.json" || true
elif [ "$DATASET" = "biored" ]; then
  [ -f "$ROOT/data/biored/$SPLIT.jsonl" ] && GOLD_JSON="$ROOT/data/biored/$SPLIT.jsonl" || true
  [ -z "$GOLD_JSON" ] && [ -f "$ROOT/data/biored/$SPLIT.json" ] && GOLD_JSON="$ROOT/data/biored/$SPLIT.json" || true
fi

if [ -s "$SRC_PREDS" ] && [ -n "$GOLD_JSON" ]; then
  echo "[INFO] Evaluating predictions: $SRC_PREDS vs $GOLD_JSON"
  python3 "$ROOT/scripts/phase7i/eval/compute_metrics.py" \
    --preds "$SRC_PREDS" --gold "$GOLD_JSON" --out "$MET" \
    --dataset "$DATASET" --split "$SPLIT" --model "$MODEL" \
    --gpu-mb "${GPU_MB:-0}" --comp-rate 0.95 >/dev/null 2>&1 || true

  if command -v jq >/dev/null 2>&1; then
    jq -c '{ds:.dataset, split:.split, m:.model, f1:.f1_micro, p:.precision_micro, r:.recall_micro, f1u:.f1_unlabeled, pc:.pred_count, gp:.gold_pairs, lat:.latency_ms, comp:(.constitutional_compliance_rate // 0)}' "$MET" > "$OUTDIR/scoreboard.json" || true
  fi
fi
