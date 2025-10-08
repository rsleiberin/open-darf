#!/usr/bin/env bash
# Read-only auditor: lists any validation_*.json with receipt_version != "0.1.0"
set -o pipefail

echo "=== Legacy Receipt Auditor (read-only) ==="
MAPFILE=()
while IFS= read -r -d '' f; do
  MAPFILE+=("$f")
done < <(find open-darf -type f -name 'validation_*.json' -print0 2>/dev/null)

if [ ${#MAPFILE[@]} -eq 0 ]; then
  echo "[info] No validation_*.json files found under open-darf/."
  exit 0
fi

LEGACY=0
for f in "${MAPFILE[@]}"; do
  ver="$(jq -r '.receipt_version // "unknown"' "$f" 2>/dev/null || echo unknown)"
  if [ "$ver" != "0.1.0" ]; then
    echo "[legacy] $f  (receipt_version=$ver)"
    LEGACY=$((LEGACY+1))
  fi
done

if [ $LEGACY -eq 0 ]; then
  echo "[ok ] All discovered receipts are v0.1.0."
else
  echo "[warn] Found $LEGACY legacy receipt(s) needing deprecation handling (manual review recommended)."
fi

echo "[done] Audit complete (no files modified)."
