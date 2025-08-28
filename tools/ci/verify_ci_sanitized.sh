#!/usr/bin/env bash
set -Eeo pipefail
# Simulate CI with a fully clean environment (no inherited exports)
exec env -i CI=true PATH="$PATH" bash tools/ci/verify_service_free.sh
