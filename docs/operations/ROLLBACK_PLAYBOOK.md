# Rollback & Safety Playbook (Phase 5)

**Principles:** flag-gate everything · deny precedence · fail-closed · snapshot before change · salvage branches for risky edits.

## Quick rollback (no code changes)
1. Disable all ML features:
   - `bash tools/rollback/feature_toggle.sh var/local/testing.env disable all`
2. Verify orchestrator returns INDETERMINATE stubs:
   - `python3 tools/try_text2nkg.py "System uses database."`
   - `python3 tools/try_temporal.py "Operated between 2018 and 2020"`

## Before schema/migration changes
1. Create salvage branch:
   - `bash tools/rollback/salvage_branch.sh`
     Options: `DO_COMMIT=1 PUSH=1` to commit and push snapshot.
2. Snapshot receipts:
   - `bash tools/rollback/snapshot_receipts.sh`

## Health checks
- Run perf/validation checks:
  - `RUN_PERF=1 python3 tools/perf/run_perf.py`
  - `python3 tools/health/checks.py` (expects latest perf receipts)

## Restore flags incrementally
- Enable one feature at a time:
  - `bash tools/rollback/feature_toggle.sh var/local/testing.env enable EXTRACTOR_TEXT2NKG`
  - Re-run `python3 tools/health/checks.py`

## Incident notes
- If validation overhead or E2E p95 exceed targets, disable features again and attach the latest receipts under `docs/audit/phase5/`.
