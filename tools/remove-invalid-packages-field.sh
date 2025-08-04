#!/bin/bash
set -euo pipefail

TOML="pyproject.toml"
BACKUP="${TOML}.invalid-packages-entry.bak"
TMP="${TOML}.tmp"

echo "📦 Backing up $TOML → $BACKUP"
cp "$TOML" "$BACKUP"

awk '
  /^\s*packages\s*=\s*\[/ {
    skip = 1
    next
  }
  /^\s*\]/ {
    if (skip) {
      skip = 0
      next
    }
  }
  { if (!skip) print }
' "$BACKUP" > "$TMP"

mv "$TMP" "$TOML"
echo "✅ Removed invalid packages = [...] field from [tool.poetry]"
