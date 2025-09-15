# Post-Grant Branch Integration Roadmap (30–90 days)

**Objective:** Systematically integrate deferred work without risking community validation infrastructure.

## 0–30 days (Stabilization & Inventory)
- Create inventory PRs for each deferred branch with `type:docs status:discussion area:infra`.
- Risk review: identify conflicting files and owners.
- Dry-run merges into temporary `chore/roadmap-*` branches; produce conflict manifests.

## 30–60 days (High-Value Merges)
- Integrate branches with low conflict surface and high operational value.
- Add regression receipts for validator, evidence packaging, and installer paths.

## 60–90 days (Historical Consolidation)
- Fold historical docs into `/docs/_archive/` with provenance links.
- Close out remaining branches with summary ADRs.

## Resource Guidance
- 1 maintainer (~4–6 hrs/week) + 1 reviewer (~2 hrs/week).
- Require green receipts and no perf regressions vs. Phase 7S baselines.

## Exit Criteria
- All targeted branches integrated or archived with ADRs.
- Validation/evidence paths unchanged or improved.
