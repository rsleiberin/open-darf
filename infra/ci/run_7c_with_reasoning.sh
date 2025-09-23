#!/usr/bin/env bash
set -euo pipefail
export REASONING_ENABLE=1
export PYTHONDONTWRITEBYTECODE=1
echo "Running Phase 7C test suite with REASONING_ENABLE=1"
pytest -q tests/phase7c
