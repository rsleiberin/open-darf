# Grant Submission Package — Phase 7S

This repository contains a packaged evidence bundle and summary for grant reviewers.

Artifacts:
- Evidence bundle: var/reports/phase7s/phase7s_evidence_bundle_20250915T002754Z.tar.gz
- Manifest: var/reports/phase7s/MANIFEST_20250915T002754Z.txt
- Bundle sha256: 2ad38cf3afbb48e0034e3372084a2b3735704ea11badbd6a5d5a7c0a55a3564f
- Bundle size (bytes): 14207

How to verify:
  1. Compute sha256 of the bundle and compare with the value above.
  2. Inspect manifest for file list, sizes, and checksums.
  3. Optionally list bundle contents: tar -tzf path/to/bundle

Suggested reviewer steps:
  - Review validation_summary.md and validation_summary.json under var/reports/phase7s
  - Open sample receipts under open-darf/var/receipts/open-darf/
  - Confirm evidence tarballs exist and unpack cleanly
  - Note environment gating for native Ubuntu 22.04 + RTX 30/40 for GPU runs

Community intake:
  - We accept external evidence tarballs and JSON receipts
  - See docs/phase7s/COMMUNITY_VALIDATION.md for instructions

Additional summaries:
  - var/reports/phase7s/timing_summary.json
  - var/reports/phase7s/timing_summary.md
