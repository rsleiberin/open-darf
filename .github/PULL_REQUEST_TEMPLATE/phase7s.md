Title: Phase 7S — Evidence, Timing, and Acceptance

## What’s in this PR
- Evidence bundle and manifest (see paths below)
- Validation + timing summaries
- Acceptance status (ALLOW | DENY | INDETERMINATE per criterion)

## Artifacts (paths)
- Bundle: var/reports/phase7s/phase7s_evidence_bundle_20250915T031621Z.tar.gz
- Manifest: var/reports/phase7s/MANIFEST_20250915T031621Z.txt
- Validation summary: var/reports/phase7s/validation_summary.{json,md}
- Timing summary:     var/reports/phase7s/timing_summary.{json,md}
- Acceptance reports: var/reports/phase7s/acceptance_status_*.{json,md}

## Reviewer Checklist
- [ ] Verify bundle sha256 matches expected:
      71e26d96d40e2b83caa69e93526f9fef54b4a20dfc3e21cb28e3508b06acd028
- [ ] Review acceptance snapshot and confirm native GPU criterion
- [ ] Confirm Makefile targets run: make finalize-phase7s, make acceptance-phase7s
- [ ] Confirm INDEX and FINAL_REPORT reflect latest bundle

## Notes
- Native validation on bare-metal Ubuntu 22.04 + RTX 30/40 is required to flip the native GPU criterion to ALLOW.
