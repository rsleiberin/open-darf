#!/usr/bin/env bash
set -euo pipefail
if [[ $# -lt 1 ]]; then echo "usage: cas_put.sh <file>" >&2; exit 2; fi
in="$1"
[[ -f "$in" ]] || { echo "[cas_put] not a file: $in" >&2; exit 2; }

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
abs="$(readlink -f "$in")"
case "$abs" in
  "$ROOT"/*) rel="${abs#$ROOT/}";;
  *) echo "[cas_put] file must be under repo root: $ROOT" >&2; exit 2;;
esac

hash="$(sha256sum "$in" | awk '{print $1}')"
size="$(stat -c%s "$in")"
ts="$(date -Is)"

# Avoid overwrite if present
if ops/bin/mc_host.sh stat local/cas/"$hash" >/dev/null 2>&1; then
  echo "[cas_put] exists: $hash" >&2
else
  ops/bin/mc_host.sh cp "/host/$rel" "local/cas/$hash" >/dev/null
  echo "[cas_put] stored (cp): $hash ($size bytes)" >&2
fi

out="docs/evidence/cas/${hash}.json"
mkdir -p "$(dirname "$out")"
printf '{"timestamp":"%s","sha256":"%s","bytes":%s,"filename":"%s"}' "$ts" "$hash" "$size" "$(basename "$in")" > "$out"
echo "[cas_put] wrote: $out" >&2
echo "$hash"
