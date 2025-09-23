#!/usr/bin/env bash
set -euo pipefail
# usage: manifest_root.sh <manifest.jsonl>
mf="$1"
[[ -f "$mf" ]] || { echo "[manifest_root] no such file: $mf" >&2; exit 2; }
# Extract sha256 values, sort, hash the concatenation with newlines
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
sed -n 's/.*"sha256":"\([a-f0-9]\{64\}\)".*/\1/p' "$mf" | sort > "$tmp"
root="$(sha256sum "$tmp" | awk "{print \$1}")"
count="$(wc -l < "$tmp" | tr -d " ")"
printf '{"manifest":"%s","count":%s,"root":"%s"}\n' "$mf" "$count" "$root"
