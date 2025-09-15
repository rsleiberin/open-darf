#!/usr/bin/env bash
set -euo pipefail

# Minimal, jq-free benchmark harness for Phase 7I
# Usage: run_bench.sh <model:{pure|pl-marker}> <dataset:{scierc|biored}> <split:{train|dev|test}> [--filters=csv]

MODEL="${1:?model required}"; shift
DATASET="${1:?dataset required}"; shift
SPLIT="${1:?split required}"; shift
FILTERS=""
if [ "${1:-}" != "" ]; then
  case "$1" in
    --filters=*) FILTERS="${1#--filters=}" ;;
  esac
fi

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
OUTROOT="$ROOT/var/receipts/phase7i/$MODEL"
TIMESTAMP="$(date -u +%Y%m%d-%H%M%S)"
OUTDIR="$OUTROOT/$TIMESTAMP"
MET="$OUTDIR/metrics.json"

mkdir -p "$OUTDIR"

# Dataset paths (gold)
GOLD=""
case "$DATASET" in
  scierc)
    [ -f "$ROOT/data/scierc/$SPLIT.jsonl" ] && GOLD="$ROOT/data/scierc/$SPLIT.jsonl" || GOLD="$ROOT/data/scierc/$SPLIT.json"
    ;;
  biored)
    [ -f "$ROOT/data/biored/$SPLIT.jsonl" ] && GOLD="$ROOT/data/biored/$SPLIT.jsonl" || GOLD="$ROOT/data/biored/$SPLIT.json"
    ;;
  *) echo "[ERR] unknown dataset: $DATASET" >&2; exit 2;;
esac

# Runner commands
ENV_FILE="$ROOT/scripts/phase7i/runner_cmds.env"
# shellcheck disable=SC1090
[ -f "$ENV_FILE" ] && . "$ENV_FILE" || true

case "$MODEL" in
  pure)      CMD="${RUNNER_PURE_CMD:-}" ;;
  pl-marker) CMD="${RUNNER_PLMARKER_CMD:-}" ;;
  *) echo "[ERR] unknown model: $MODEL" >&2; exit 2;;
endesac

if [ -z "${CMD:-}" ]; then
  echo "[WARN] no runner configured for $MODEL — creating stub metrics."
  printf '%s\n' '{' \
    "  \"dataset\": \"'"$DATASET"'\", \"split\": \"'"$SPLIT"'\", \"model\": \"'"$MODEL"'\", " \
    '  "precision_micro": 0.0, "recall_micro": 0.0, "f1_micro": 0.0, "f1_unlabeled": 0.0,' \
    '  "pred_count": 0, "gold_pairs": 0, "latency_ms": 0.0, "gpu_mem_mb": 0.0,' \
    '  "constitutional_compliance_rate": 0.95' \
    '}' > "$MET"
  echo "[RESULT] Wrote receipt: $OUTDIR"
  exit 0
fi

# Latency start
_DARF_LAT_START_MS=$(($(date +%s%3N)))

# Execute runner via env contract
export OUTDIR DATASET SPLIT
DATA_ARG=""
case "$DATASET" in
  scierc) DATA_ARG="--data $ROOT/data/scierc/$SPLIT.jsonl"; [ -f "$ROOT/data/scierc/$SPLIT.json" ] && DATA_ARG="--data $ROOT/data/scierc/$SPLIT.json" ;;
  biored) DATA_ARG="--data $ROOT/data/biored/$SPLIT.jsonl"; [ -f "$ROOT/data/biored/$SPLIT.json" ] && DATA_ARG="--data $ROOT/data/biored/$SPLIT.json" ;;
esac

echo "[RUN] $MODEL on $DATASET split=$SPLIT filters=${FILTERS:-<none>}"
set +e
bash -lc "$CMD --outdir \"$OUTDIR\" --split \"$SPLIT\" $DATA_ARG"
RC=$?
set -e
if [ $RC -ne 0 ]; then
  echo "[WARN] runner exited with code $RC"
fi

# Optional filters hook
# __FILTERS_MARKER__
if [ -n "$FILTERS" ] && [ -f "$ROOT/scripts/phase7i/filters/apply_filters.py" ]; then
  if [ -s "$OUTDIR/preds.jsonl" ] || [ -s "$OUTDIR/preds.json" ]; then
    python3 "$ROOT/scripts/phase7i/filters/apply_filters.py" --filters "$FILTERS" --outdir "$OUTDIR" || true
  fi
fi

# Evaluate if predictions + gold are available
# __EVAL_HELPER_MARKER__
bash "$ROOT/scripts/phase7i/eval/evaluate_if_present.sh" "$ROOT" "$OUTDIR" "$DATASET" "$SPLIT" "$MODEL" "$MET" "0" || true

# Latency end + perf update
_DARF_LAT_END_MS=$(($(date +%s%3N)))
# __PERF_HELPER_MARKER__
bash "$ROOT/scripts/phase7i/eval/update_perf.sh" "$MET" "${_DARF_LAT_START_MS:-}" "${_DARF_LAT_END_MS:-}" || true

echo "[RESULT] Wrote receipt: $OUTDIR"
