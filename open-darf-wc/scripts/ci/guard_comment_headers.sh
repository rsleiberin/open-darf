#!/usr/bin/env bash
set -euo pipefail
shopt -s globstar nullglob
viol=0
for f in **/*.sh **/*.ps1 **/*.yml **/*.yaml Dockerfile* *compose.yml *compose.yaml; do
  [[ -f "$f" ]] || continue
  head -n 80 "$f" | grep -q "Header: Purpose" || { echo "[fail] missing header in $f"; viol=1; }
done
exit $viol
