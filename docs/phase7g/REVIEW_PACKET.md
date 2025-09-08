# Phase 7G — Review Packet

**Timestamp:** 2025-09-08T19:26:04Z

## Executive Summary
- RE baseline (heuristic v6) = **F1_micro 0.3368**, **unlabeled 0.5313**, **compliance 1.0**.
- Smokes: **Packaging/Lifecycle PASS**, **E2E Bootstrap PASS** (gates: F1≥0.20, compliance≥0.95) using bridged v6 metrics.
- Metrics governance: **All receipts schema-validated OK**.
- PURE / PL-Marker: bridges & wrappers ready; receipts present. Full model runs intentionally deferred (no deps).

## Primary Artifacts
- Baseline metrics (source of truth): `var/receipts/phase7g/relation_baseline/run/20250907-205327_v6/metrics.json`
- Finalize receipt dir: `var/receipts/phase7g/finalize/20250908-192059`
- Latest packaging smoke: `var/receipts/phase7g/packaging_smoke/20250908-183142`
- Latest PURE bridge: `var/receipts/phase7g/pure_runs/20250908-052010`
- Latest PL-Marker bridge: `var/receipts/phase7g/plmarker_runs/20250908-051836`
- Error analysis (normalized parser): `var/receipts/phase7g/re_error_analysis/20250908-044925_syntaxfix/`
- Data contract: `docs/phase7g/DATA_CONTRACT_SCIERC.md`
- Error analysis notes: `docs/phase7g/ERROR_ANALYSIS_NOTES.md`
- Status rollup: `docs/phase7g/STATUS.md`
- Merge plan: `docs/phase7g/MERGE_PLAN.md`

## PRs
- **#384** — Relation Extraction Baseline (E1 pass) — Ready for review
- **#385** — Config consolidation + CI validation — Ready for review
- **#386** — PURE baseline plan + harness skeleton — **Draft** (keep open for model baselines)

## Reviewer Notes
- Gates enforced in `scripts/relex_ci_smoke.py` (bridged receipts; tolerant compliance key handling).
- Packaging stub emits no schema-breaking metrics; packaging receipts backfilled to schema v1.
- Universal parser normalized spans to exclusive end; 455/455 normalized relations generated for SciERC dev.

