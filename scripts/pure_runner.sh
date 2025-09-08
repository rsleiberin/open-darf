#!/usr/bin/env bash
set -Eeuo pipefail
OUTDIR="var/receipts/phase7g/pure_runs/$(date -u +%Y%m%d-%H%M%S)"
mkdir -p "$OUTDIR"
python3 apps/relex/pure/runner.py --dataset_dir "data/scierc_norm" --split dev --outdir "$OUTDIR" | tee "$OUTDIR/runner_cli.out"
echo "Wrote: $OUTDIR"
