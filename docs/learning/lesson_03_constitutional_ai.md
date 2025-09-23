# Lesson 3 — Constitutional AI in Open-DARF (Primer)

We encode operational constraints as **principles** and enforce them during implementation.

**Core behaviors**
- **DENY precedence**: any DENY beats ALLOW.
- **Tri-state** decisions: ALLOW | DENY | INDETERMINATE.
- **Audit receipts**: every critical step writes a machine-checked receipt.

You can see a minimal seed in Neo4j (unique `Principle` id) applied during bring-up.

**Reflect**
- Where did you see DENY precedence encoded?  
- Which receipts prove health on your machine today?
