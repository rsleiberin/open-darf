# Branch Consolidation Plan — Phase 7S (Deferral Strategy)

**Purpose:** Document deferral of non-essential branches to protect the grant timeline while preserving development value.

## Deferred Branches (with rationale)
- phase7p/wsl-cuda-torch-rca — Historical WSL2 debugging artifacts; not grant-critical.
- phase7q/wsl-cuda-pivot — Strategic decision documentation; integrate post-grant.
- phase7o/receipts-and-prs — Receipts infra; evaluate utility vs. minimal evidence path later.
- phase7l/safe-closeout — Historical integration; post-grant consolidation.
- phase7h/e2e-receipts-acceptance — Dev infra; not essential for validation campaign.

## Preservation Strategy
- Keep remote branches intact; no rebase/force-push.
- Snapshot findings in `/docs/phase7*/` as needed.
- Capture perf/evidence receipts into `var/receipts/phase7s/deferrals/` when pulled locally.

## Post-Grant Integration Heuristics
- **Impact > Effort** first.
- Prefer linear merges; avoid squashing historical analysis branches if they contain evidence.
- Maintain "no direct pushes to main"; use chore/merge-* staging branches.

## Acceptance Criteria
- This plan exists in repo, referenced by Phase 7S acceptance criteria.
- Each deferred branch has a one-paragraph justification and integration notes.

## Remote Branch Inventory (captured 2025-09-14)
- chore/phase7l-safe-closeout
- chore/phase7o-receipts-and-prs
- feat/phase7h-e2e-receipts-acceptance
- feat/phase7i-benchmark-optimization
- main
- phase7p/wsl-cuda-torch-rca
- phase7q/wsl-cuda-pivot
