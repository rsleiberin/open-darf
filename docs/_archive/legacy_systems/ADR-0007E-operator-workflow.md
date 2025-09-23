# ADR-0007E: Operator Vote Workflow (Deterministic, DENY Precedence)

**Status:** Accepted (Phase 7E)  
**Context:** Need a governed, deterministic operator input path for conflict resolution.

## Decision
- Define a minimal JSON schema for operator votes with fields:
  - `decision_context`, `votes[] {principle, decision, weight, rationale}`, optional `dependencies`, `interactions`.
- Deterministic resolver:
  - Any `DENY` → `REJECTED`
  - Else if ALLOW mass ≥ 0.5 → `ACCEPTABLE`
  - Else → `PENDING`
- Add `validate_votes.py` to lint/validate inputs.

## Consequences
- Enables redacted, reproducible evidence trails.
- Keeps enrichment additive; does not alter base decisions.

## Alternatives considered
- Non-deterministic/training-based resolution — rejected for 7E due to reproducibility and governance concerns.
