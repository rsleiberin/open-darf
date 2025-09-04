# Phase 7D Sprint Plan (→ Oct 1 deadline)

## Objectives
- Finish Group 3 (conflict patterns surfaced in explanations; rationale export).
- Complete Group 6 guardrails (CI enforced; broader E2E scenarios).
- Expand Group 9 evidence with real enriched audits (flagged runs).
- Keep 7C guarantees intact; sub-µs reasoning overhead maintained.

## Milestones
- M1: CI green on 7C+7D (this PR) — owner: Impl Agent — due: Sept 6
- M2: Conflict pattern surfacing — owner: Impl Agent — due: Sept 10
- M3: Evidence gallery (redacted samples) — owner: Impl Agent — due: Sept 15
- M4: Grant pack freeze (Groups 9–10) — owner: Impl Agent — due: Sept 25

## Quality Gates
- No degradation of 7C gating.
- REASONING_ENABLE must be additive-only.
- Perf: reasoning p95 remains sub-µs in harness.

## Workstream Leads
- Reasoning Infra: Impl Agent
- Evidence & Docs: Impl Agent
- Arch Review: Architect

## Tracking
- Receipts in docs/audit/*
- Evidence in docs/evidence/phase7d/*
- CI: .github/workflows/phase7d.yml
