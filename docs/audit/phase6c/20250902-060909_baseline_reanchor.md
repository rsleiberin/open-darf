# Phase-6C Baseline Re-anchor (20250902-060909)

- Inputs: var/datasets/normalized/biored_concept/{train,dev,test}.jsonl
- Mapping: var/datasets/heuristic_map.json (train-only)
- Receipts: dev/test → var/receipts/phase6c/relations/*_relations_scores_concept_*.json
- Summary: var/receipts/phase6c/relations/summary_baseline_20250902-060909.json

Notes: Makefile recipe separators currently need cleanup; used direct module calls.
