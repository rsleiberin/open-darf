# Verification (TLA/TLC)

This directory contains public **TLA+ specifications** and **TLC model checking evidence** for the open-darf system. Evidence artifacts for Class-A specs from **Phase 8E** are stored under `evidence/tla/class_a/`.

**Class-A TLC:** pos PASS=0 / FAIL=10 • neg PASS=9 / FAIL=0 • total runs=19

## Evidence Index
- Logs: `evidence/tla/class_a/logs/`
- Receipts (SHA-256): `evidence/tla/class_a/receipts/`
- Summary (JSON): `evidence/tla/class_a/summaries/summary.json`

## Reproduce Locally
Requirements: Java 11+, `tla2tools.jar`.

Example:
```bash
java -jar /path/to/tla2tools.jar -tool -deadlock -config verification/tla/classA_cfgs/pos/CA_DenyPrecedence.cfg verification/tla/classA_specs/CA_DenyPrecedence.tla
```

## Results (Phase 8E)
| Module                      | Cfg                             | Label | Status | Log                                                                                                          |
| --------------------------- | ------------------------------- | ----- | ------ | ------------------------------------------------------------------------------------------------------------ |
| CA_AnchorToEmbedIntegrity   | CA_AnchorToEmbedIntegrity_neg   | neg   | PASS   | evidence/tla/class_a/logs/CA_AnchorToEmbedIntegrity__CA_AnchorToEmbedIntegrity_neg__20250927T215019Z.out     |
| CA_AnchorToEmbedIntegrity   | CA_AnchorToEmbedIntegrity_pos   | pos   | FAIL   | evidence/tla/class_a/logs/CA_AnchorToEmbedIntegrity__CA_AnchorToEmbedIntegrity_pos__20250927T215017Z.out     |
| CA_AuditTrailIntegrity      | CA_AuditTrailIntegrity          | pos   | FAIL   | evidence/tla/class_a/logs/CA_AuditTrailIntegrity__CA_AuditTrailIntegrity__20250927T215018Z.out               |
| CA_AuditTrailIntegrity      | CA_AuditTrailIntegrity          | neg   | PASS   | evidence/tla/class_a/logs/CA_AuditTrailIntegrity__CA_AuditTrailIntegrity__20250927T215020Z.out               |
| CA_DenyPrecedence           | CA_DenyPrecedence               | pos   | FAIL   | evidence/tla/class_a/logs/CA_DenyPrecedence__CA_DenyPrecedence__20250927T215018Z.out                         |
| CA_DenyPrecedence           | CA_DenyPrecedence               | neg   | PASS   | evidence/tla/class_a/logs/CA_DenyPrecedence__CA_DenyPrecedence__20250927T215020Z.out                         |
| CA_Neo4jConstraintSchema    | CA_Neo4jConstraintSchema_neg    | neg   | PASS   | evidence/tla/class_a/logs/CA_Neo4jConstraintSchema__CA_Neo4jConstraintSchema_neg__20250927T215019Z.out       |
| CA_Neo4jConstraintSchema    | CA_Neo4jConstraintSchema_pos    | pos   | FAIL   | evidence/tla/class_a/logs/CA_Neo4jConstraintSchema__CA_Neo4jConstraintSchema_pos__20250927T215017Z.out       |
| CA_ProvenanceChainValidity  | CA_ProvenanceChainValidity      | pos   | FAIL   | evidence/tla/class_a/logs/CA_ProvenanceChainValidity__CA_ProvenanceChainValidity__20250927T215018Z.out       |
| CA_ProvenanceChainValidity  | CA_ProvenanceChainValidity      | neg   | PASS   | evidence/tla/class_a/logs/CA_ProvenanceChainValidity__CA_ProvenanceChainValidity__20250927T215020Z.out       |
| CA_Smoke                    | CA_Smoke_neg                    | neg   | PASS   | evidence/tla/class_a/logs/CA_Smoke__CA_Smoke_neg__20250927T215019Z.out                                       |
| CA_Smoke                    | CA_Smoke_pos                    | pos   | FAIL   | evidence/tla/class_a/logs/CA_Smoke__CA_Smoke_pos__20250927T215018Z.out                                       |
| CA_SpanAuthorization        | CA_SpanAuthorization_neg        | neg   | PASS   | evidence/tla/class_a/logs/CA_SpanAuthorization__CA_SpanAuthorization_neg__20250927T215020Z.out               |
| CA_SpanAuthorization        | CA_SpanAuthorization_pos        | pos   | FAIL   | evidence/tla/class_a/logs/CA_SpanAuthorization__CA_SpanAuthorization_pos__20250927T215018Z.out               |
| CA_SpanPreservesConstraints | CA_SpanPreservesConstraints_neg | neg   | PASS   | evidence/tla/class_a/logs/CA_SpanPreservesConstraints__CA_SpanPreservesConstraints_neg__20250927T215020Z.out |
| CA_SpanPreservesConstraints | CA_SpanPreservesConstraints_pos | pos   | FAIL   | evidence/tla/class_a/logs/CA_SpanPreservesConstraints__CA_SpanPreservesConstraints_pos__20250927T215018Z.out |
| CA_TriStateCompleteness     | CA_TriStateCompleteness         | pos   | FAIL   | evidence/tla/class_a/logs/CA_TriStateCompleteness__CA_TriStateCompleteness__20250927T215018Z.out             |
| CA_TriStateCompleteness     | CA_TriStateCompleteness         | neg   | PASS   | evidence/tla/class_a/logs/CA_TriStateCompleteness__CA_TriStateCompleteness__20250927T215020Z.out             |
| CC_A_cc                     | CC_A_cc.quick                   | pos   | FAIL   | evidence/tla/class_a/logs/CC_A_cc__CC_A_cc.quick__20250927T215018Z.out                                       |
