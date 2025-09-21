#!/usr/bin/env bash
set -euo pipefail
ROOT="${1:-$PWD}"
viol=0
# target human-facing files; skip unreadable, generated, and backups
while IFS= read -r -d '' f; do
  if grep -q '```' "$f" 2>/dev/null; then
    echo "[LINT] Found 3-backtick fence in: $f"
    viol=1
  fi
done < <(find "$ROOT" \
           -type d \( -path "$ROOT/.git" -o -path "$ROOT/node_modules" -o -path "$ROOT/results" -o -path "$ROOT/.cache" -o -path "$ROOT/infra/neo4j/init" \) -prune -o \
           -type f \( -name "*.md" -o -name "*.mdx" -o -name "*.sh" -o -name "*.ps1" \) -readable -print0 2>/dev/null)
if [ "$viol" -ne 0 ]; then
  echo "[LINT] FAIL: Replace 3-backtick fences with tildes (~~~) or 4-space indents."
  exit 2
fi
echo "[LINT] PASS: No 3-backtick fences found."
