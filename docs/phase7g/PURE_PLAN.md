# Phase 7G — PURE Baseline Implementation Plan

## Scope
Integrate a PURE-style relation extraction baseline on SciERC dev, building on our heuristic v6 milestone (F1≈0.337). Keep CI green by failing closed on missing deps and emitting receipts.

## Milestones
- **M0 (now):** Scaffold + plan (done).
- **M1:** Minimal PURE runner with pretrained weights; JSON metrics receipt (micro P/R/F1, unlabeled F1, latency).
- **M2:** Repro harness + deterministic seeds; per-run receipts under `var/receipts/phase7g/pure_runs/<ts>/`.
- **M3:** Parameter sweep skeleton; docs + scoreboard update.
- **M4:** Direction to PL-Marker path (stretch).

## Guardrails
- Constitutional post-filters remain in post-processing.
- CI-safe: when `torch/transformers` absent → runner prints `"status":"deps_missing"` and exits 0 for smoke jobs.

## Interfaces
- **Runner:** `python apps/relex/pure/runner.py --dataset_dir data/scierc_norm --split dev --outdir <dir>`
- **Receipts:** `metrics.json`, `scoreboard_compact.json`, `runner_stdout.json`

## Risks & Mitigations
- **Env churn:** Start with CPU-only wheels; pin exact versions.
- **Label drift:** Reuse current label-map learning.
- **Runtime:** Target < 10 min dev inference; subset if needed.

## Exit Targets (aligned)
- **RE-E2 (near-term):** F1 (SciERC) ≥ 0.50
- **RE-E3 (stretch):** F1 (SciERC) ≥ 0.70 (PL-Marker path)

## Enablement v0 (2025-09-07T23:08:29Z)
- Added `requirements/pure.txt` (pinned)
- Added `scripts/setup_pure_env.sh` (CPU wheels; idempotent)
- Added `scripts/pure_dev_run.sh` wrapper
- Added opt-in CI workflow `.github/workflows/pure-optin.yml` gated by label `ci:run-pure`

## Bridge Mode (2025-09-07T23:47:33Z)
- `apps/relex/pure/runner.py` supports `--bridge-from-baseline` (default: True).
- When PURE deps are absent, it imports the **best heuristic baseline** `metrics.json` into a new `pure_runs/<ts>/` outdir and writes schema-compliant receipts.
- This validates the PURE harness, evaluator, and schema without heavy deps.
