#!/usr/bin/env bash
set -euo pipefail

# Scan only public-facing Markdown:
# - Include: root *.md, docs/*.md and docs subfolders commonly public
# - Exclude: internal/phase/history/implementation/agent/audit/etc., VCS, CI, vendor, results/evidence/var, infra init dirs
issues=0

public_md() {
  # Build an allowlist-oriented find with necessary prunes
  find . \
    \( -path './.git' -o -path './.github' -o -path './node_modules' -o -path './results' -o -path './evidence' -o -path './var' \) -prune -o \
    \( -path './docs/implementation' -o -path './docs/_archive' -o -path './docs/agent' -o -path './docs/audit' -o -path './docs/handoff' -o -path './docs/phase*' -o -path './infra/neo4j/init' \) -prune -o \
    \( -type f -name '*.md' \) -print0 2>/dev/null
}

while IFS= read -r -d '' f; do
  in_fence=0
  lineno=0
  while IFS= read -r line || [ -n "$line" ]; do
    lineno=$((lineno+1))
    if [[ "$line" =~ ^\`\`\` ]]; then
      in_fence=$((1-in_fence))
      continue
    fi
    if (( in_fence == 1 )) && [[ "$line" == *'```'* ]]; then
      echo "[lint] Nested fence in $f:$lineno"
      issues=1
    fi
  done < "$f"
done < <(public_md)

if (( issues != 0 )); then
  echo "[lint] Markdown fence policy violations found."
  exit 2
fi

echo "[lint] Markdown fence policy OK."
