# Community Validation Guide

Help us validate Open-DARF across diverse environments.

## What to Run
    bash ./quick_demo.sh

## What to Capture
- OS, CPU, GPU model and VRAM
- Python and Docker versions
- Run duration (approximate)
- results/summary.json
- results/ports_live_receipt.json (if containers used)

## How to Report
Open a new issue using the "Community Validation Run" template and paste:
- System info
- Any warnings shown
- The contents of results/summary.json

Optionally attach:
- grant_evidence_package.tar.gz
