# Phase 7G — Merge Plan (RE Baseline + Config/CI)

## Scope
This plan proposes merging:
- **#384**: Relation Extraction Baseline — E1 achieved
- **#385**: Config consolidation v1 + CI validation

## Preconditions
- Main is protected; merges occur via PR (squash).
- CI smoke gates exist:
  - RE smoke gate: F1_micro ≥ 0.20 and compliance ≥ 0.95
  - Config validation workflow
  - Packaging/lifecycle smoke

## Evidence / Receipts
- Best heuristic baseline (v6): `var/receipts/phase7g/relation_baseline/run/20250907-205327_v6/metrics.json`
- Error-analysis harness: latest normalized run (455/455 resolved): see newest under `var/receipts/phase7g/re_error_analysis/*/`
- PURE/PL-Marker bridges (opt-in CI ready): newest under `var/receipts/phase7g/pure_runs/` and `var/receipts/phase7g/plmarker_runs/`
- E2 readiness scoreboard: `docs/scoreboards/phase7g/e2_readiness.json`

## Merge Steps
1. Mark #384 and #385 **Ready for Review**.
2. Ensure CI passes (RE smoke F1/compliance; config validate; packaging smoke).
3. Squash-merge each PR into `main` (maintainers).
4. Post-merge:
   - Tag `phase7g-e1` (optional).
   - Keep #386 open for model baselines; continue opt-in CI via labels.

## Risk Notes
- No `.tla/.cfg` modifications.
- DENY precedence and fail-closed posture preserved in smoke gates.
- Protected branches respected (no direct pushes).
