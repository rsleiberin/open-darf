# Phase 7S — Release Notes

- Generated: 2025-09-15T03:30:36Z

## Summary
- Evidence receipts: 4 (WSL:4 · Native:0)
- Install success: 4 — 100.0% (95% CI 51.0–100.0%)
- Minimal run success: 3 — 75.0% (95% CI 30.1–95.4%)
- Evidence packaging success: 4 — 100.0% (95% CI 51.0–100.0%)
- Timing probe samples: 2 — Sub-ms ratio: 100.0% (95% CI 34.2–100.0%)

## Bundle
- Path: var/reports/phase7s/phase7s_evidence_bundle_20250915T031621Z.tar.gz
- Manifest: var/reports/phase7s/MANIFEST_20250915T031621Z.txt
- sha256: 71e26d96d40e2b83caa69e93526f9fef54b4a20dfc3e21cb28e3508b06acd028
- size (bytes): 21679

## Acceptance Snapshot (top excerpt)
# Phase 7S — Acceptance Status

- Generated: 20250915T031621Z

- C1_repo_consolidation_docs: ALLOW — branch_consolidation_plan.md & post_grant_integration_roadmap.md
- C2_validation_flow_operational: ALLOW — receipts=4, evidence_ok=4
- C3_timing_probe_integrated: ALLOW — samples_with_timing=2
- C4_evidence_bundle_ready: ALLOW — bundle=present
- C5_native_ubuntu_gpu_evidence: DENY — pass if native gate passed or non-WSL oneclick with run+evidence OK

## Artifacts

- validation_summary.json: var/reports/phase7s/validation_summary.json
- timing_summary.json: var/reports/phase7s/timing_summary.json
- bundle: var/reports/phase7s/phase7s_evidence_bundle_20250915T031621Z.tar.gz
- manifest: var/reports/phase7s/MANIFEST_20250915T031621Z.txt
- sample oneclick receipts:
  - open-darf/var/receipts/open-darf/oneclick_DESKTOP-30KIIKV_20250915T000648Z.json
  - open-darf/var/receipts/open-darf/oneclick_DESKTOP-30KIIKV_20250915T001644Z.json
  - open-darf/var/receipts/open-darf/oneclick_DESKTOP-30KIIKV_20250915T002133Z.json
  - open-darf/var/receipts/open-darf/oneclick_DESKTOP-30KIIKV_20250915T003731Z.json
- native gate receipts:
  - var/receipts/phase7s/native_check_DESKTOP-30KIIKV_20250915T012112Z.json
  - var/receipts/phase7s/native_check_DESKTOP-30KIIKV_20250915T012459Z.json
