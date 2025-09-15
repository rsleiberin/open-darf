#!/usr/bin/env bash
set -euo pipefail
echo "[quickstart] running installer, minimal validate, evidence packaging"
"$(dirname "$0")/../install.sh"
"$(dirname "$0")/../validate/run_minimal.sh"
"$(dirname "$0")/../validate/generate_evidence.sh" || true
echo "[quickstart] done"
