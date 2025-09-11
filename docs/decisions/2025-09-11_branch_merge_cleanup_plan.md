# Branch Merge & Cleanup Plan — 2025-09-11

## Context
- `feat/phase7h-e2e-receipts-acceptance` is **Phase 8 scaffolding**; keep off `main` for now.
- Base branch: `origin/main`. See divergence report in `docs/audit/`.

## Recommended Strategy (Plan only — no changes executed)
1) **Phase 7L consolidation**
   - Target: `chore/phase7l-safe-closeout`
   - Fold WIP branches into chore via `--no-ff`:
     - `phase7l_wip_20250910-221121`
     - `phase7l_wip_20250910-222451`
     - `phase7l_pre_safepoint_20250910-221420`
   - PR chore → `main`, then prune the WIP branches after merge

2) **Phase 8 scaffold isolation**
   - Create `feat/phase8-e2e-scaffold` from `origin/main`
   - Merge `feat/phase7h-e2e-receipts-acceptance` into it (history preserved)
   - PR later → `main` after GPU runtime pivot lands

3) **Benchmark lane**
   - Rebase `feat/phase7i-benchmark-optimization` onto updated `main`
   - Run short CI (lint/unit), then PR → `main`

4) **Stray `r`**
   - If trivial: `git tag archive/r-2025-09-11 r` then delete branch
   - If useful: rename to `exp/r-*` and keep out of release PRs

## Safety
- No destructive actions until architect approval
- Require CI on all PRs; use `--no-ff` for consolidation merges
