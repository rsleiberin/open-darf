# Operator Conflict Vote — Quickstart (7E)

Minimal operator input to supply structured votes for conflict resolution.

## Schema
See:
- docs/operators/conflict_vote_schema.yaml
- tools/constitutional/reasoning/operator_vote_schema.json

## Example (YAML)
    version: "vote_schema_v1"
    decision_context:
      id: "audit-abc123"
      description: "Content flag triage for sample"
    votes:
      - principle: "Safety.DeniedContent"
        decision: "DENY"
        weight: 1.0
        rationale: "Contains disallowed instruction"
      - principle: "Explainability.Trace"
        decision: "ALLOW"
        weight: 0.4
        rationale: "Trace provided and logged"

## Validate & Resolve
    python tools/constitutional/reasoning/validate_votes.py my_vote.yaml --print

Resolution rules:
- Any DENY → REJECTED
- Else sum of ALLOW.weight ≥ 0.5 → ACCEPTABLE
- Else → PENDING
