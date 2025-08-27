#!/usr/bin/env bash
set -eE -o pipefail
trap - ERR EXIT RETURN DEBUG || true

STAMP="$(date -u +%Y%m%d-%H%M%S)"
SRC="var/receipts"
DEST="docs/audit/phase5/${STAMP}-post"
mkdir -p "$DEST"
if [ -d "$SRC" ]; then
  rsync -a "$SRC"/ "$DEST"/ >/dev/null 2>&1 || cp -R "$SRC"/* "$DEST"/ 2>/dev/null || true
fi
# Build index
{
  echo "# Post-mutation snapshot (${STAMP})"
  echo
  if [ -d "$DEST" ]; then
    find "$DEST" -type f | sed "s#^#- #"
  else
    echo "- (empty)"
  fi
} > "$DEST/index.md"
echo "✓ Snapshot written to $DEST"
