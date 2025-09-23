#!/usr/bin/env bash
set -euo pipefail
ROOT="$1"; f="$2"
abs="$(readlink -f "$f")"
rel="${abs#$ROOT/}"
read -r sha bytes < <(ops/bin/hash_file.sh "$abs")
h="$(ops/bin/cas_put.sh "$abs" 2>/dev/null | tail -n1)"
if [[ "$h" != "$sha" ]]; then
  echo "[worker] ERROR: CAS key mismatch for $rel" >&2
  exit 3
fi
printf '{"path":"%s","sha256":"%s","bytes":%s}\n' "$rel" "$sha" "$bytes"
