#!/usr/bin/env bash
set -Eeuo pipefail
# Local-only perf runner (CI-safe): requires RUN_PERF=1 to execute tests
export RUN_PERF="${RUN_PERF:-1}"
pytest -q tests/performance -q
