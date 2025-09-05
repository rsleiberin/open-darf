# Dependency & Interaction Analysis (7E)

This note explains how operator votes should capture dependencies and interactions between principles.

- Dependencies: list principles that must be satisfied for this vote to be applicable.
- Interactions: list principles that are affected by the outcome of this vote.

Resolution summary:
- Strict DENY precedence — any DENY across votes → REJECTED.
- Else weighted ALLOW mass ≥ 0.5 → ACCEPTABLE.
- Else → PENDING.

Rationale guidance:
- Keep rationales free of PII.
- Reference precedent IDs when applicable.
