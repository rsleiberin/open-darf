#!/usr/bin/env bash
set -euo pipefail

: "${OUTDIR:?OUTDIR not set}"
: "${DATASET:?DATASET not set}"
: "${SPLIT:?SPLIT not set}"

usage(){ echo "Usage: OUTDIR=... DATASET=... SPLIT=... run_pure.sh [--simulate] --data <path> --split <split> --outdir <path> [-- extra model args]"; }

DATA_PATH="" ; OUT=""
SIMULATE=0
while [ $# -gt 0 ]; do
  case "$1" in
    --data) DATA_PATH="$2"; shift 2 ;;
    --split) shift 2 ;; # split already in env
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
  # emit small dummy preds
  echo '{"head":"X","tail":"Y","relation":"REL"}' > "$OUT/preds.jsonl"
  echo "[WRAP/PURE] simulate → $OUT/preds.jsonl"
  exit 0
fi

# >>> Replace the command below with your real PURE invocation <<<
# Example:
# /opt/venvs/pure/bin/python /path/to/PURE/run.py --data "$DATA_PATH" --split "$SPLIT" --out "$OUT/preds.jsonl" "$@"
echo "[WRAP/PURE] ERROR: real PURE command not configured in wrapper."
exit 4
