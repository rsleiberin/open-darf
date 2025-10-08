# Validation Evidence Receipts

Validation receipts submitted by anonymous validators testing Open-DARF.

## Privacy
- Anonymous validator IDs only (random hex)
- No usernames or identifying information
- Platform and timestamp included

## For Validators
Run validation with evidence submission:
- Linux: ./scripts/core/validate_with_evidence.sh
- Windows: .\scripts\core\validate_with_evidence.ps1

Your receipt is saved locally and you can optionally commit it to the repo.

## For Documentation
The aggregated_metrics.json file provides statistics that documentation can reference directly.

## Deprecation Policy (v0.1.0)
- Only receipts with `"receipt_version": "0.1.0"` are considered canonical.
- Deprecated receipts (older formats) are quarantined under `_DEPRECATED/` for provenance only and should not be used.
