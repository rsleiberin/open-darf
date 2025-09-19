#!/usr/bin/env bash
set -euo pipefail
err=0
while IFS= read -r f; do
  if grep -q '^```' "$f"; then
    echo "[fence-violation] $f"
    err=1
  fi
done < <(git ls-files '*.md' '*.adoc' 2>/dev/null)
exit $err
