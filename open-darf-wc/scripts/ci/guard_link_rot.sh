#!/usr/bin/env bash
set -euo pipefail
# Lightweight: extract http(s) links from docs and test with curl --head (timeouts short)
shopt -s globstar nullglob
viol=0
for f in **/*.md **/*.adoc; do
  [[ -f "$f" ]] || continue
  # naive URL scrape
  urls=$(grep -Eo '(https?://[^ )"]+)' "$f" | sort -u || true)
  for u in $urls; do
    curl -fsI --max-time 5 "$u" >/dev/null || { echo "[warn] link check failed: $u ($f)"; viol=1; }
  done
done
exit $viol
