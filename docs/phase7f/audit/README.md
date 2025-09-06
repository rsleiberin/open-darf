# 7F/D17 — Audit & Provenance Schema

This enforces:
- Constitutional decisions trail (ALLOW/DENY/INDETERMINATE)
- Propagation latency (p95_ms)
- Revocation scope and cycle flag
- Provenance (agent, activity, entity, bundle)

Validate: `scripts/phase7f/validate_audit.py` → `var/receipts/phase7f/audit_validation/*/summary.json`
