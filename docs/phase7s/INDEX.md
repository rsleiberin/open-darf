# Phase 7S — Artifact Index

Generated: 2025-09-15T02:03:20Z  
Branch: chore/phase7s-index

## Evidence Bundle
- Bundle: var/reports/phase7s/phase7s_evidence_bundle_20250915T020047Z.tar.gz
- Manifest: var/reports/phase7s/MANIFEST_20250915T020047Z.txt
- sha256: bd47dc24deb90e03890a8c71407e6518d0bb660c6b21c6d91a6ada62535280ed
- size (bytes): 19549

## Summaries
- Validation summary (JSON): var/reports/phase7s/validation_summary.json
- Validation summary (MD):   var/reports/phase7s/validation_summary.md
- Timing summary (JSON):     var/reports/phase7s/timing_summary.json
- Timing summary (MD):       var/reports/phase7s/timing_summary.md

## Receipts & Evidence
- One-click receipts: open-darf/var/receipts/open-darf/
- Evidence tarballs (open-darf/): open-darf/open-darf-report-*.tar.gz
- Evidence tarballs (root): ./open-darf-report-*.tar.gz
- Community intake receipts: var/receipts/community/
- Native checklist receipts: var/receipts/phase7s/native_check_*.json

## Commands (copy/paste)
- Aggregate: ./scripts/phase7s/aggregate_evidence.sh
- Timing summary: scripts/phase7s/extract_timing_from_tarballs.py
- Package bundle: ./scripts/phase7s/package_evidence.sh
- Build release kit: ./scripts/phase7s/build_open_darf_release.sh
- Intake evidence: make intake-community files="<paths>"
- Open-DARF quickstart: (cd open-darf && make quickstart)
- Open-DARF oneclick: (cd open-darf && make oneclick)
- Native host checklist: bash scripts/phase7s/native_host_checklist.sh

## Notes
- Native GPU validation requires Ubuntu 22.04 LTS on bare metal with RTX 30/40 (≥8GB VRAM).
- Timing probe is embedded in evidence tarballs as timing_probe.json.

## Acceptance
- Acceptance gate reports: var/reports/phase7s/acceptance_status_*.json
- Acceptance gate reports: var/reports/phase7s/acceptance_status_*.md
