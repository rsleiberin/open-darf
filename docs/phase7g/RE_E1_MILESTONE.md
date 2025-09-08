# Phase 7G — Relation Extraction Milestone RE-E1 (PASS)
**Timestamp (UTC):** 2025-09-07T23:45:53Z

## Best Baseline (SciERC-dev)
- Model: `heuristic-stdlib-v6`
- Precision: 0.457143
- Recall: 0.266667
- F1 (micro): **0.336842**
- F1 (unlabeled): 0.53125
- Pred: 128  Gold: 118
- Compliance: 1.0
- Latency (ms): 5.35
- Receipt: `var/receipts/phase7g/relation_baseline/run/20250907-205327_v6/metrics.json`

## Notes
- Direction-aware lexical rules; negation & distance filters (v6 best).
- E2 target (PURE path): F1 ≥ 0.50 on SciERC-dev.
