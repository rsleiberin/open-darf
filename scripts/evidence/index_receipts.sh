#!/usr/bin/env bash
# Build an index of validation receipts without touching contents.
# Emits JSON with: path, receipt_version, size_bytes, mtime_iso
set -e -o pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
OUT="$ROOT/open-darf/evidence/validation_receipts/index.json"

# Gather candidates within open-darf only
mapfile -d '' FILES < <(find "$ROOT/open-darf" -type f -name 'validation_*.json' -print0 2>/dev/null || true)

# Start JSON array
printf '[\n' > "$OUT"
first=1
for f in "${FILES[@]}"; do
  # Skip the index file itself if it matches the pattern
  [ "$f" = "$OUT" ] && continue

  # Extract fields safely
  ver="$(jq -r '.receipt_version // "unknown"' "$f" 2>/dev/null || echo unknown)"
  size=$(wc -c < "$f" | tr -d ' ')
  mtime=$(date -u -r "$f" '+%Y-%m-%dT%H:%M:%SZ' 2>/dev/null || stat -f "%Sm" -t "%Y-%m-%dT%H:%M:%SZ" "$f" 2>/dev/null || echo "")

  # Comma handling
  if [ $first -eq 0 ]; then
    printf ',\n' >> "$OUT"
  else
    first=0
  fi

  # Normalize path relative to repo root for portability
  rel="${f#$ROOT/}"

  # Write entry
  jq -n --arg path "$rel" --arg ver "$ver" --arg mtime "$mtime" --argjson size "$size" \
    '{path:$path, receipt_version:$ver, size_bytes:$size, mtime_iso:$mtime}' >> "$OUT"
done
printf '\n]\n' >> "$OUT"

echo "[index] Wrote $(printf "%s" "$OUT" | sed "s|$ROOT/||")"
