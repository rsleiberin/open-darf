#!/usr/bin/env bash
set -euo pipefail
FILE="$1"; shift
mkdir -p "$(dirname "$FILE")"
{
  flock 9
  printf "%s\n" "$*"
} 9>>"$FILE"
