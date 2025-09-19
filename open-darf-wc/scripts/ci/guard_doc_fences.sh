#!/usr/bin/env bash
set -euo pipefail
# Fails if triple backticks appear in Markdown/AsciiDoc within open-darf-wc
shopt -s globstar nullglob
viol=0
for f in **/*.md **/*.adoc; do
  [[ -f "$f" ]] || continue
  if grep -q '```' "$f"; then
    echo "[fail] triple backticks found in $f"
    viol=1
  fi
done
exit $viol
