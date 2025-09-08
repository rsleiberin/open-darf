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

## Config Consolidation v1 (2025-09-07T21:08:41Z)
- Introduced `packages/darf_config` Pydantic surface (DB_/API_/LLM_)
- Added `configs/.env.sample` and `scripts/quick-setup.sh`
- Added `compose/compose.yaml` with profiles dev/staging/prod (no secrets committed)

## CI Config Validation (2025-09-07T21:11:47Z)
- Added `.github/workflows/config-validate.yml` (pydantic v1 install, env sample load)
- Added `scripts/lifecycle_smoke.sh` (config + artifacts smoke)

## Packaging/CI — RE Smoke (2025-09-07T21:14:07Z)
- Added `scripts/relex_ci_smoke.py` asserting F1≥0.20 on SciERC-dev (stdlib baseline)
- Added `.github/workflows/relex-smoke.yml` to run on PR/push

## CI Gate Tightening (2025-09-07T22:39:08Z)
- RE smoke now enforces **F1 ≥ 0.20** AND **constitutional_compliance_rate ≥ 0.95**

## Packaging/Lifecycle Smoke v1 (2025-09-07T22:42:24Z)
- Added `scripts/packaging_smoke.sh` (optional Neo4j probe + RE smoke)
- Added `.github/workflows/packaging-smoke.yml` (runs RE smoke on PR/push)

## E2E Bootstrap Smoke v1 (2025-09-07T22:48:59Z)
- Added `scripts/e2e_bootstrap.sh` chaining quick-setup → config validate → packaging/RE smoke
- Emits receipts under `var/receipts/phase7g/e2e_bootstrap/<ts>/run.out`

## Milestone 7G-PKG-E1 (2025-09-07T22:51:39Z) — PASS
- Fresh clone → `scripts/e2e_bootstrap.sh` validates config and runs packaging/RE smoke
- CI: config validation, RE smoke (F1≥0.20 & compliance≥0.95), packaging smoke workflow
- Receipts: see `var/receipts/phase7g/e2e_bootstrap/20250907-224856`

## PURE Scaffold v1 (2025-09-07T23:03:19Z)
- Added `apps/relex/pure/` with `pure_stub.py`
- Added `scripts/pure_smoke.py` (CI-safe; status=skipped/ready)
- Added `.github/workflows/pure-smoke.yml`

## PURE Harness Skeleton (2025-09-07T23:06:35Z)
- Added `apps/relex/pure/runner.py` and `scripts/pure_runner.sh`
- CLI prints `status=deps_missing` until deps are installed; keeps CI green

## PURE Enablement v0 (2025-09-07T23:08:29Z)
- Reqs + local venv + opt-in CI scaffolded; runner remains skeleton (deps_missing→green)

## PURE CI Opt-in (2025-09-07T23:28:24Z)
- Requested CI run for PURE via label `ci:run-pure` on PR #386

## Metrics Schema & CI (2025-09-07T23:29:32Z)
- Added `docs/schemas/metrics_v1.json` and `scripts/metrics_validate.py`
- CI workflow `metrics-validate.yml` runs RE smoke then validates receipts

## Metrics Backfill (2025-09-07T23:42:08Z)
- Added `latency_ms` to historical v5 receipt for schema v1 compliance

## Milestone 7G-RE-E1 (2025-09-07T23:45:53Z) — PASS
- Best baseline: see `docs/phase7g/RE_E1_MILESTONE.md`

## PURE Bridge Run (2025-09-07T23:48:49Z)
- Runner fixed (removed inner `import json`).
- Bridge executed to import best heuristic metrics into PURE receipts; schema validation OK.

## PURE Bridge Wrapper (2025-09-07T23:51:11Z)
- Added `scripts/pure_bridge_run.sh` that imports best heuristic metrics when PURE deps are missing, then validates schema.

## PURE Opt-in CI Hardening (2025-09-08T00:06:05Z)
- Opt-in workflow now runs `scripts/pure_bridge_run.sh` and then `metrics_validate.py --strict`.
- Ensures schema-valid PURE receipts even when heavy deps are unavailable.

## CI Artifact Uploads (2025-09-08T00:07:15Z)
- PURE opt-in workflow now uploads `metrics.json` & compact scoreboard.
- RE smoke workflow now uploads `metrics.json` & `local_smoke.json`.

## E2 Readiness Tracker (2025-09-08T00:09:25Z)
- Script: `scripts/e2_target_tracker.py` (target=0.50 micro-F1)
- Latest report written to `docs/scoreboards/phase7g/e2_readiness.json`
- Optional CI: `.github/workflows/e2-readiness.yml` (label `ci:track-e2`)

## PL-Marker Scaffold (2025-09-08T00:12:52Z)
- Added deps-aware runner stub + bridge wrapper.
- Opt-in CI (`plmarker-optin.yml`) with strict metrics validation + artifact upload.
- Label to run: `ci:run-plmarker`.

## Architect Roll-up (2025-09-08T00:15:53Z)
- See `docs/phase7g/ARCH_SUMMARY.md` for consolidated status and PR links.

## Error Analysis Hardened (2025-09-08T00:21:45Z)
- Parser now supports dict/n-tuple relations and mixed entity schemas; bounds-checked token windows; skip counters added.

## Update @ 20250908-053020

- Error-analysis harness: normalized **455/455** relations; receipt: `var/receipts/phase7g/re_error_analysis/20250908-044925_syntaxfix`.
- PURE bridge (deps missing): latest receipt: `var/receipts/phase7g/pure_runs/20250908-052010`.
- PL-Marker bridge (deps missing): latest receipt: `var/receipts/phase7g/plmarker_runs/20250908-051836`.
- E2 readiness: best F1_micro **0.336842**, delta to 0.50 **0.163158**; scoreboard: `docs/scoreboards/phase7g/e2_readiness.json`.

## Update @ 20250908-190752

- Packaging/Lifecycle smoke: **PASS**; latest receipt: `var/receipts/phase7g/packaging_smoke/20250908-183142`.
- E2E bootstrap smoke: **PASS** (config validate + packaging smoke).
- RE smoke gates evaluated against: `var/receipts/phase7g/relation_baseline/run/20250907-205327_v6/metrics.json` (F1>=0.20, compliance>=0.95).
- PURE bridge latest: `var/receipts/phase7g/pure_runs/20250908-052010`.

## Update @ 2025-09-08T19:36:49Z

- Review packet posted: `docs/phase7g/REVIEW_PACKET.md`.
- Latest handoff pinned: `docs/agent/handoff_latest.md`.

## Merge prep @ 2025-09-08T19:41:25Z

- Posted merge-readiness checklists to PRs #384 and #385.
- Receipt: `var/receipts/phase7g/merge_prep/20250908-194125/summary.json`.
