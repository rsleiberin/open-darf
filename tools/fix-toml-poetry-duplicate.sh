#!/bin/bash
set -euo pipefail

TOML="pyproject.toml"
TMP="${TOML}.tmp"
BACKUP="${TOML}.conflict-duplicate-header"

echo "🧪 Backing up $TOML → $BACKUP"
cp "$TOML" "$BACKUP"

awk '
  BEGIN {
    header_seen = 0
    suppress = 0
  }
  /^\[tool\.poetry\]/ {
    if (header_seen == 1) {
      suppress = 1
      next
    }
    header_seen = 1
  }
  /^\[/ && suppress == 1 {
    suppress = 0
  }
  {
    if (!suppress) print
  }
' "$TOML" > "$TMP"

mv "$TMP" "$TOML"
echo "✅ Removed duplicate [tool.poetry] block from $TOML"
