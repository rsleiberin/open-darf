#!/bin/bash
set -euo pipefail

TOML="pyproject.toml"
BACKUP="${TOML}.invalid-deps-entry.bak"
TMP="${TOML}.tmp"

echo "🧪 Backing up $TOML → $BACKUP"
cp "$TOML" "$BACKUP"

awk '
  BEGIN { in_block = 0; skipping = 0 }
  /^\[tool\.poetry\]/ { in_block = 1; print; next }
  /^\[/ && in_block == 1 { in_block = 0 }
  in_block && /^\s*dependencies\s*=\s*\[/ {
    skipping = 1
    next
  }
  skipping && /^\s*\]/ {
    skipping = 0
    print "[tool.poetry.dependencies]"
    next
  }
  {
    if (!skipping) print
  }
' "$BACKUP" > "$TMP"

mv "$TMP" "$TOML"
echo "✅ Replaced invalid dependencies block with [tool.poetry.dependencies]"
