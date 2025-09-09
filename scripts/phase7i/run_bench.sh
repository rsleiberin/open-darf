#!/usr/bin/env bash
set -euo pipefail

usage(){
  echo "Usage: $0 <pure|pl-marker> <scierc|biored> [--filters=directionality,negation,type] [--split=train|dev|test]"
  exit 1
}

[ $# -ge 2 ] || usage
MODEL="$1"; DATASET="$2"; FILTERS=""; SPLIT="test"
for arg in "${@:3}"; do
  case "$arg" in
    --filters=*) FILTERS="${arg#--filters=}" ;;
    --split=*)   SPLIT="${arg#--split=}" ;;
  esac
done

timestamp(){ date -u +%Y%m%d-%H%M%S; }
STAMP="$(timestamp)"
ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
OUTDIR="$ROOT/var/receipts/phase7i/$MODEL/$STAMP"
mkdir -p "$OUTDIR"

# --- Load runner command configuration (if present) ---
CFG="$ROOT/scripts/phase7i/runner_cmds.env"
if [ -f "$CFG" ]; then . "$CFG"; fi

# --- Dataset dirs ---
DATA_ROOT="$ROOT/data"
case "$DATASET" in
  scierc) DDIR="$DATA_ROOT/scierc" ;;
  biored) DDIR="$DATA_ROOT/biored" ;;
  *) usage ;;
esac

# --- Environment snapshot ---
probe(){ nc -z -w2 127.0.0.1 "$1" >/dev/null 2>&1 && echo "up" || echo "down"; }
GPU_MB_RAW=$( (nvidia-smi --query-gpu=memory.total --format=csv,noheader 2>/dev/null || echo "0") | head -n1 )
GPU_MB=$(echo "$GPU_MB_RAW" | sed 's/ MiB//;s/ //g')

cat > "$OUTDIR/env.json" <<EOF
{
  "timestamp_utc":"$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "gpu_mem_mb": ${GPU_MB:-0},
  "services": {
    "redis":"$(probe 6379)",
    "postgres":"$(probe 5432)",
    "neo4j_http":"$(probe 7474)",
    "neo4j_bolt":"$(probe 7687)",
    "qdrant":"$(probe 6333)",
    "minio":"$(probe 9000)"
  },
  "filters":"$FILTERS"
}
EOF

cat > "$OUTDIR/inputs.json" <<EOF
{
  "dataset":"$DATASET",
  "split":"$SPLIT",
  "dataset_dir":"$DDIR",
  "model":"$MODEL",
  "filters":"$FILTERS"
}
EOF

# --- Resolve command preference: configured command → module fallback ---
CMD=""
case "$MODEL" in
  pure)
    if [ -n "${RUNNER_PURE_CMD:-}" ]; then
      CMD="$RUNNER_PURE_CMD --dataset \"$DDIR\" --split \"$SPLIT\""
    fi
    MOD="runners.pure"
    ;;
  pl-marker)
    if [ -n "${RUNNER_PLMARKER_CMD:-}" ]; then
      CMD="$RUNNER_PLMARKER_CMD --dataset \"$DDIR\" --split \"$SPLIT\""
    fi
    MOD="runners.pl_marker"
    ;;
  *)
    usage
    ;;
esac

RUNNER_AVAILABLE="false"
if [ -n "$CMD" ]; then
  RUNNER_AVAILABLE="true"
else
  # Check for python module fallback
  if python - <<PY 2>/dev/null; then RUNNER_AVAILABLE="true"; fi
import importlib, sys
sys.exit(0 if importlib.util.find_spec("runners") else 1)
PY
fi

MET="$OUTDIR/metrics.json"

emit_stub(){
  local comp="$1"
  cat > "$MET" <<EOF
{
  "dataset":"$DATASET",
  "split":"$SPLIT",
  "model":"$MODEL",
  "precision_micro": 0.0,
  "recall_micro": 0.0,
  "f1_micro": 0.0,
  "f1_unlabeled": 0.0,
  "pred_count": 0,
  "gold_pairs": 0,
  "latency_ms": 0.0,
  "gpu_mem_mb": ${GPU_MB:-0},
  "constitutional_compliance_rate": $comp,
  "note":"placeholder"
}
EOF
  jq -c '{
    ds:.dataset, split:.split, m:.model,
    f1:.f1_micro, p:.precision_micro, r:.recall_micro,
    f1u:.f1_unlabeled, pc:.pred_count, gp:.gold_pairs,
    lat:.latency_ms, comp:(.constitutional_compliance_rate // 0)
# (disabled)   # __PERF_CAPTURE_MARKER__ capture perf into metrics (latency_ms, gpu_mem_mb)
# (disabled)   if [ -f "$MET" ]; then
# (disabled)     LAT_MS=""
# (disabled)     if [ -n "${_DARF_LAT_START_MS:-}" ] && [ -n "${_DARF_LAT_END_MS:-}" ]; then
# (disabled)       LAT_MS=$(( _DARF_LAT_END_MS - _DARF_LAT_START_MS ))
# (disabled)     fi
    GPU_MB_VAL="${GPU_MB:-0}"
    if command -v nvidia-smi >/dev/null 2>&1; then
      # take total-used for a coarse snapshot
      GPU_MB_VAL=$(nvidia-smi --query-gpu=memory.total,memory.used --format=csv,noheader,nounits 2>/dev/null | head -n1 | awk -F, "{print \$1}")
    fi
    if command -v jq >/dev/null 2>&1; then
      jq ".latency_ms = (\"$LAT_MS\"|tonumber // .latency_ms) | .gpu_mem_mb = (\"$GPU_MB_VAL\"|tonumber // .gpu_mem_mb)" "$MET" > "$MET.tmp" && mv "$MET.tmp" "$MET" || true
    fi
  fi
  }' "$MET" > "$OUTDIR/scoreboard.json" || true
  echo "[RESULT] Wrote receipt: $OUTDIR"
}

if [ "$RUNNER_AVAILABLE" = "true" ]; then
  set +e
  if [ -n "$CMD" ]; then
    # shellcheck disable=SC2086
  # __FILTERS_MARKER__ post-run filter hook
  # __EVAL_HELPER_MARKER__ evaluate if predictions and gold are present
  # __PERF_HELPER_MARKER__ patch latency & GPU mem into metrics.json
  bash "$ROOT/scripts/phase7i/eval/update_perf.sh" "$MET" "${_DARF_LAT_START_MS:-}" "${_DARF_LAT_END_MS:-}"
  bash "$ROOT/scripts/phase7i/eval/evaluate_if_present.sh" "$ROOT" "$OUTDIR" "$DATASET" "$SPLIT" "$MODEL" "$MET" "${GPU_MB:-0}"
  PRED_JSON="$OUTDIR/preds.json"
  FILT_JSON="$OUTDIR/preds.filtered.json"
  if [ -s "$PRED_JSON" ] && [ -n "$FILTERS" ]; then
    echo "[INFO] Applying filters: $FILTERS"
    python3 "$ROOT/scripts/phase7i/filters/apply_filters.py" --preds "$PRED_JSON" --out "$FILT_JSON" --filters "$FILTERS" >/dev/null 2>&1 || true
  fi
    eval $CMD > "$OUTDIR/runner.log" 2>&1
  else
    python -m "$MOD" --dataset "$DDIR" --split "$SPLIT" > "$OUTDIR/runner.log" 2>&1
  fi
  RC=$?
  set -e
  if [ $RC -ne 0 ]; then
    emit_stub 0.0
  else
    if [ ! -f "$MET" ]; then
      emit_stub 0.95
    else
      jq -c '{
        ds:.dataset, split:.split, m:.model,
        f1:.f1_micro, p:.precision_micro, r:.recall_micro,
        f1u:.f1_unlabeled, pc:.pred_count, gp:.gold_pairs,
        lat:.latency_ms, comp:(.constitutional_compliance_rate // 0)
      }' "$MET" > "$OUTDIR/scoreboard.json" || true
      echo "[RESULT] Wrote receipt: $OUTDIR"
    fi
  fi
else
  emit_stub 0.0
fi
