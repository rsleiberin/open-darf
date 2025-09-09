#!/usr/bin/env bash
set -euo pipefail

: "${OUTDIR:?OUTDIR not set}"
: "${DATASET:?DATASET not set}"
: "${SPLIT:?SPLIT not set}"

usage(){ echo "Usage: OUTDIR=... DATASET=... SPLIT=... run_plmarker.sh [--simulate] --data <path> --split <split> --outdir <path> [-- extra model args]"; }

DATA_PATH="" ; OUT=""
SIMULATE=0
while [ $# -gt 0 ]; do
  case "$1" in
    --data) DATA_PATH="$2"; shift 2 ;;
    --split) shift 2 ;;
    --outdir) OUT="$2"; shift 2 ;;
    --simulate) SIMULATE=1; shift ;;
    --help|-h) usage; exit 0 ;;
    --) shift; break ;;
    *) break ;;
  esac
done

OUT="${OUT:-$OUTDIR}"
mkdir -p "$OUT"

if [ "$SIMULATE" -eq 1 ]; then
  echo '{"head":"A","tail":"B","relation":"REL"}' > "$OUT/preds.jsonl"
  echo "[WRAP/PL-Marker] simulate → $OUT/preds.jsonl"
  exit 0
fi

# >>> Replace the command below with your real PL-Marker invocation <<<
# Example:
# /opt/venvs/plmarker/bin/python /path/to/PL-Marker/run.py --data "$DATA_PATH" --split "$SPLIT" --out "$OUT/preds.jsonl" "$@"
echo "[WRAP/PL-Marker] ERROR: real PL-Marker command not configured in wrapper."
exit 4
