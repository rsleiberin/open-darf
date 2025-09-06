# Phase 7F — Synthesis Orchestrator (read-only)

CLI to fuse vector and graph rankings via RRF(k=60) with optional constraint demotion.

## Usage

scripts/phase7f/synthesis_orchestrator.py --vector var/receipts/phase7f/dryrun_exec/<ts>/synthesis_exec.json \
  --graph  var/receipts/phase7f/dryrun_exec/<ts>/synthesis_exec.json \
  --topk 10 --rrf_k 60

Provide `--constraints` with a JSON list of pairs like `[["docA","docE"]]` to demote forbidden co-occurrences.
