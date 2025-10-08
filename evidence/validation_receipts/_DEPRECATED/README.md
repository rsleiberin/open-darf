# Deprecated Validation Receipts

This folder quarantines **non-canonical** validation receipts that do **not** conform to the v0.1.0 schema
(11 ordered top-level keys with `"receipt_version": "0.1.0"`). These artifacts remain here for provenance,
but they should not be used for current validation.

- Canonical receipts live under: `open-darf/var/receipts/open-darf/`
- Linux v0.1.0 generator: `scripts/internal/comprehensive_validation_v010.sh`
- Windows v0.1.0 generator: `scripts/internal/comprehensive_validation_v010.ps1`
- Order-aware validator (non-fatal): `scripts/evidence/validate_receipt_v010.sh`
