#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
SRC="$ROOT/var/receipts/phase7i"
DST="$SRC/_archive/$(date -u +%Y%m%d-%H%M%S)"
if [ ! -d "$SRC" ]; then
  echo "[ARCHIVE] No receipts directory at $SRC — nothing to archive."
  exit 0
fi
mkdir -p "$DST"
# Move only model subdirs, keep _archive/
shopt -s nullglob
moved=0
for d in "$SRC"/*; do
  base="$(basename "$d")"
  [ "$base" = "_archive" ] && continue
  mv "$d" "$DST"/
  moved=$((moved+1))
done
echo "[ARCHIVE] Moved $moved item(s) into $DST"
