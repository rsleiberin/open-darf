# 7F/D18 — End-to-end Validation

Aggregates receipts:
- Synthesis (fused.json), Propagation p95, Revocation (plan/commit), Dependency accuracy, CI gates.
Checks budgets: synthesis<2s, propagation<100ms, revocation<5s, dep_acc≥99.9%.
Outputs: `var/receipts/phase7f/e2e/<ts>/summary.json`.
