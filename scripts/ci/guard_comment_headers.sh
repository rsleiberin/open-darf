#!/usr/bin/env bash
set -euo pipefail
err=0
check() {
  local f="$1"
  if ! grep -q "Header: Purpose" "$f"; then
    echo "[missing-header] $f"
    err=1
  fi
}
while IFS= read -r f; do check "$f"; done < <(git ls-files '*.sh' '*.ps1' '*.yml' '*.yaml' 2>/dev/null)
exit $err
