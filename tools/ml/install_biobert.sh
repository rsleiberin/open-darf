#!/usr/bin/env bash
set -Eeo pipefail
python3 -m pip install --upgrade pip
python3 -m pip install -r requirements/ml_bio.txt
echo "✓ BioBERT-related deps installed (local)"
