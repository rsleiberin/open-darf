Phase 7I evaluator (scaffold)

Converts runner predictions (JSONL or JSON array) into DARF strict metrics.json:
precision_micro, recall_micro, f1_micro, f1_unlabeled, pred_count, gold_pairs,
latency_ms, gpu_mem_mb, constitutional_compliance_rate.

Expected prediction format is flexible; we normalize common patterns into:
{ "head": "...", "tail": "...", "relation": "RELTYPE" }

Gold files (default locations):
- SciERC: data/scierc/<split>.jsonl or .json
- BioRED: data/biored/<split>.jsonl or .json

If your runner schema differs, extend adapters.py:normalize_item.
