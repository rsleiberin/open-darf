# Phase 7D — Multi-Principle Conflict Resolution

- **Governance rule**: Strict **DENY precedence** — any DENY ⇒ REJECTED (fail-closed).
- **Weights**: `REASONING_WEIGHTS_JSON` (JSON object) used only when no DENY is present, to quantify ALLOW mass.
- **Determinism**: Order-independent (commutative) and idempotent (duplicates collapse by severity).
- **Output**: `(decision, rationale)` where rationale records rule path and weight evidence.
- **No `.tla/.cfg` touched.** Compatible with 7C blocking guarantees.
