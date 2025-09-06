# 7F/D16 — Tri-state Enforcement (ALLOW / DENY / INDETERMINATE)

- **Deny precedence:** any DENY at a boundary yields overall DENY.
- **Fail-closed:** unknown inputs → INDETERMINATE, not ALLOW.
- **Integration points:** synthesis orchestrator triage; revocation commit preflight guard.
- **Receipts:** validated via unit tests under `tests/phase7f/test_tristate.py`.
