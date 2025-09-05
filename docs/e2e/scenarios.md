# Phase 7E — E2E Scenarios (Proposed)

Run with `REASONING_ENABLE=1` and capture enriched audits (redact before committing).

## Scenario A: Policy Gate with Conflicting Principles
- Input: curated conflict cases with explicit votes (Safety DENY vs Explainability ALLOW).
- Expectation: REJECTED (DENY precedence); enriched rationale captured.

## Scenario B: Weighted ALLOW without DENY
- Input: low-confidence ALLOW votes totaling <0.5.
- Expectation: PENDING; rationale includes dependency/interaction notes.

## Scenario C: Consistency Check with Precedents
- Input: decision candidates near prior precedents; governance overrides present.
- Expectation: ACCEPTABLE if weights ≥0.5 and no DENY; citations to valid precedents.

Artifacts to produce:
- Redacted enriched audits (JSONL)
- Scenario receipts under `docs/evidence/phase7e/enriched_examples/`
