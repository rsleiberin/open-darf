#!/usr/bin/env bash
set -euo pipefail
if command -v nproc >/dev/null 2>&1; then nproc
elif command -v getconf >/dev/null 2>&1; then getconf _NPROCESSORS_ONLN
elif command -v sysctl >/dev/null 2>&1; then sysctl -n hw.ncpu
else echo 1
fi
