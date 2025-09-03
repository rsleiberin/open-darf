# Phase-6C Relation Full Run
- Commit: `27b0191`
- Input (selected): `data/biored/train.jsonl` (copied to `var/datasets/biored_relations_full.jsonl`)
- Output receipt: `var/receipts/phase6c/validation/biored_relations_scores_full.json`

## BioRED metrics (heuristic predictor)
- Precision: 0
- Recall: 0
- F1: 0
- Support: 1

_Notes:_
- Dataset auto-discovered by scanning repository for JSONL with "entities" and "relations".
- Heuristic is deterministic and simple; scores will reflect its limits on real data.
- Relation metrics remain **non-gated** in CI.
