#!/usr/bin/env bash
set -euo pipefail
# usage: hash_file.sh <path>
f="$1"
[[ -f "$f" ]] || { echo "not a file: $f" >&2; exit 2; }
sha="$(sha256sum "$f" | awk '{print $1}')"
bytes="$(stat -c%s "$f")"
printf '%s %s\n' "$sha" "$bytes"
