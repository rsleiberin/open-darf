#!/bin/bash
set -euo pipefail

TOML="pyproject.toml"
BACKUP="${TOML}.bak"
PKG_ENTRY='[tool.poetry]\npackages = [{ include = "darf_core" }]'

if grep -q '^\[tool\.poetry\]' "$TOML"; then
  echo "✅ [tool.poetry] block already exists."
  exit 0
fi

echo "📦 Patching $TOML with [tool.poetry] shim..."
cp "$TOML" "$BACKUP"

awk -v patch="$PKG_ENTRY" '
  BEGIN { patched = 0 }
  {
    print
    if (!patched && /^\[build-system\]/) {
      print patch
      patched = 1
    }
  }
' "$BACKUP" > "$TOML"

echo "✅ Inserted [tool.poetry] shim after [build-system]."
