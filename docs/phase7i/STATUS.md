# Phase 7I — Benchmark Optimization: STATUS

**Primary**: Lift SciERC F1_micro ≥ 0.50 (from ~0.33 baseline).
**Secondary**: Strengthen competitive positioning (DARF vs PURE vs PL-Marker).
**Invariant**: Constitutional compliance ≥ 0.95.

## Current State
- Infra checks: Redis/Neo4j/Qdrant/MinIO/PostgreSQL — UP
- GPU: Detected (nvidia-smi OK)
- Datasets: TBD (probed at runtime)

## Next Milestones
- Run PURE & PL-Marker on SciERC/BioRED
- Aggregate scoreboards under `docs/scoreboards/phase7i/`
- Apply directionality/negation/type-gating filters and re-benchmark
- Draft competitive comparison & open PR

## Packaging Update (20250909-180021 UTC)
- Receipts manifest: var/receipts/phase7i/RECEIPTS_MANIFEST_20250909-180021.json
- Archive: var/receipts/phase7i/manifest_20250909-180021.zip

## Schema Alignment (20250909-180240 UTC)
- Metrics schema aligned to architect strict fields.
- New receipts generated (stub-valid) for PURE & PL-Marker on SciERC/BioRED.
- Aggregated scoreboard: docs/scoreboards/phase7i/scoreboard_20250909-180240.jsonl
- Archive: var/receipts/phase7i/manifest_20250909-180240.zip

## Legacy Repair (20250909-180405 UTC)
- Patched legacy metrics to strict schema; revalidated; refreshed scoreboard.
- Aggregated scoreboard: docs/scoreboards/phase7i/scoreboard_20250909-180405.jsonl
- Archive: var/receipts/phase7i/manifest_20250909-180405.zip

## Session summary 20250909-180947 UTC
Infra verified and running. Schema aligned to strict metrics. Legacy receipts repaired.
Harness replaced and smoke tested. Runner command layer added.
Next focus: real baseline executions for PURE and PL-Marker on SciERC and BioRED.

## Orchestrator & Aggregation 20250909-181414 UTC
- scripts/phase7i/run_all.sh to execute PURE/PL-Marker on SciERC & BioRED.
- scripts/phase7i/aggregate_scoreboard.py emits docs/scoreboards/phase7i/summary_*.md.
- Next: set runner_cmds.env and run scripts/phase7i/run_all.sh --split=test; then re-run aggregation.

## PR Link
https://github.com/rsleiberin/darf-source/pull/388

## Acceptance Snapshot 20250909-181847 UTC
See docs/phase7i/ACCEPTANCE_REPORT.md

## CI Setup 20250909-182452 UTC
Workflow: .github/workflows/phase7i_ci.yml validates metrics, aggregates scoreboards, and posts acceptance snapshot on PR.
Developer shortcuts in Makefile: bench-all, aggregate, accept, verify-splits, bootstrap.
