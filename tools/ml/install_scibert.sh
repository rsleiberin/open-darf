#!/usr/bin/env bash
set -Eeo pipefail
# Local-only helper; CI remains service-free unless explicitly invoked by a job.
python3 -m pip install --upgrade pip
python3 -m pip install -r requirements/ml.txt
echo "✓ SciBERT-related deps installed (local)"
