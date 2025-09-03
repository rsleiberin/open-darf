# Phase-6C Relation Full Run (mapped heuristic)
- Commit: `27b0191`
- Input: `var/datasets/biored_relations_full.jsonl`
- Mapping: `var/datasets/heuristic_map.json`
- Output: `var/receipts/phase6c/validation/biored_relations_scores_full_mapped.json`

## BioRED metrics
- Precision: 0.5
- Recall: 1
- F1: 0.6666666666666666
- Support: 1

_Notes:_ Mapping selects the majority label per entity-type pair; still deterministic & hermetic.
