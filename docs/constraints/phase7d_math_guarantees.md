# Phase 7D — Mathematical Guarantees Framework

**Tri-State Semantics:** ACCEPTABLE | REJECTED | PENDING  
- Default: PENDING ⇒ blocked at every gate (fail-closed).

**Deny Precedence Theorem (Resolver):**  
If ∃ principle with vote=DENY ⇒ decision=REJECTED, independent of weights.

**Commutativity & Idempotence:**  
Conflict resolution is order-independent; duplicate votes collapse by severity.

**Invariance Under Enrichment:**  
For any audit event `e`, enrichment `E(e)` preserves base fields and decision.

**Receipt-Backed Claims:**  
Percentile timings recorded in `docs/audit/*` and verified in CI-like runners.

*Note:* This document outlines guarantees; no `.tla/.cfg` modifications performed.
