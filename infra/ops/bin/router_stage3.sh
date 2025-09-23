#!/usr/bin/env bash
set -euo pipefail
# usage: router_stage3.sh <file> [<file>...]
mkdir -p var/router/accept var/router/pending var/router/deny docs/evidence/router
ts="$(date -Is)"
for f in "$@"; do
  [[ -f "$f" ]] || { echo "[router] skip (not a file): $f" >&2; continue; }
  sha="$(sha256sum "$f" | awk '{print $1}')"
  dec="$(ops/bin/tri_state_validator.sh "$f")"  # prints decision only
  base="$(basename -- "$f")"
  case "$dec" in
    ALLOW)
      ln -sf "$(realpath "$f")" "var/router/accept/${sha}-${base}"
      dest="var/router/accept/${sha}-${base}"
      ;;
    PENDING)
      cp -f "$f" "var/router/pending/${sha}-${base}"
      dest="var/router/pending/${sha}-${base}"
      ;;
    DENY|*)
      cp -f "$f" "var/router/deny/${sha}-${base}"
      dest="var/router/deny/${sha}-${base}"
      ;;
  esac
  out="docs/evidence/router/route_${sha}_$(date +%s).json"
  {
    printf '{'
    printf '"timestamp":"%s","src":"%s","dest":"%s","sha256":"%s","decision":"%s"' "$ts" "$f" "$dest" "$sha" "$dec"
    printf '}'
  } > "$out"
  echo "[router] %s -> %s (%s)" "$f" "$dest" "$dec"
done
