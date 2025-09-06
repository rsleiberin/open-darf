# 7F/B11 — Deterministic Revocation Scenarios

- Scenario files (tracked): `docs/phase7f/revocation/scenarios/*.json`
- Evaluator: `scripts/phase7f/dep_accuracy.py` → writes receipts under `var/receipts/phase7f/dep_acc/*/metrics.json`
- CI gates ingest `dependency_accuracy` from the latest metrics receipt.
