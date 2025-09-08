# Phase 7G — Status (bootstrap)

## Summary
- Preflight (Neo4j): PASS
- Repo hygiene: PASS
- Opening PR to begin relation extraction baseline, config consolidation, and packaging validation.

## Receipts (latest)
- See `RECEIPTS_INDEX.md` for canonical paths.

## Baseline Precheck (2025-09-07T20:20:22Z)
- SciERC dir: `data/scierc_norm` (files: 4)
- BioRED dir: `data/biored_norm` (files: 3)
- Python probe: see `var/receipts/phase7g/relation_baseline/precheck/20250907-202022/python_probe.json` (if present)
- Metrics schema: `var/receipts/phase7g/relation_baseline/precheck/20250907-202022/metrics_schema.json`

## Baseline Run (2025-09-07T20:23:23Z)
- Dataset: SciERC dev — model `heuristic-stdlib`
- Detected schema: `scierc_original`
- P/R/F1 (micro): 0.000/0.000/0.000  (unlabeled F1: 0.000)
- Pairs: pred=0 gold=0  latency=0.24ms
- Receipt: `var/receipts/phase7g/relation_baseline/run/20250907-202323`

## Baseline Run v3 (2025-09-07T20:28:40Z)
- Dataset: SciERC dev — model `heuristic-stdlib-v3`
- Detected schema: `scierc_original`
- v3 P/R/F1 (micro): 0.000/0.000/0.000  (unlabeled F1: 0.279); skipped: spans=611, rels=337
- Pairs: pred=162 gold=118  latency=19.8ms
- Receipt: `var/receipts/phase7g/relation_baseline/run/20250907-202840_v3`

## Baseline Run v4 (2025-09-07T20:34:02Z)
- Dataset: SciERC dev — model `heuristic-stdlib-v4`
- P/R/F1 (micro): 0.000/0.000/0.000  (unlabeled F1: 0.336)
- Compliance: 0.986
- Pairs: pred=138 gold=118  latency=18.1ms
- Receipt: `var/receipts/phase7g/relation_baseline/run/20250907-203402_v4`

## Baseline Run v5 (2025-09-07T20:42:21Z)
- Dataset: SciERC dev — model `heuristic-stdlib-v5`
- P/R/F1 (micro): 0.180/0.195/0.187  (unlabeled F1: 0.276)
- Compliance: 0.985
- Pairs: pred=128 gold=118
- Receipt: `var/receipts/phase7g/relation_baseline/run/20250907-204220_v5`

## Baseline Run v6 (2025-09-07T20:53:27Z)
- Dataset: SciERC dev — model `heuristic-stdlib-v6`
- P/R/F1 (micro): 0.457/0.267/0.337  (unlabeled F1: 0.531)
- Pairs: pred=128 gold=118  latency=5.35ms
- Receipt: `var/receipts/phase7g/relation_baseline/run/20250907-205327_v6`

## Baseline Run v7 (2025-09-07T20:56:35Z)
- Dataset: SciERC dev — model `heuristic-stdlib-v7`
- P/R/F1 (micro): 0.278/0.167/0.208  (unlabeled F1: 0.548)
- Pairs: pred=78 gold=118  latency=4.91ms
- Receipt: `var/receipts/phase7g/relation_baseline/run/20250907-205635_v7`

## Milestone 7G-RE-E1 (2025-09-07T20:58:52Z) — PASS
- Best model: `heuristic-stdlib-v6` on SciERC dev
- P/R/F1 (micro): 0.457/0.267/0.337
- Receipt: `var/receipts/phase7g/relation_baseline/run/20250907-205327_v6`
