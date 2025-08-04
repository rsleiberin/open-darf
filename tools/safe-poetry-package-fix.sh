#!/bin/bash
set -euo pipefail

TOML_PATH="pyproject.toml"
PACKAGE_ENTRY='packages = [{ include = "darf_core" }]'

if [[ ! -f "$TOML_PATH" ]]; then
  echo "❌ pyproject.toml not found."
  exit 1
fi

if ! grep -q '^\[tool\.poetry\]' "$TOML_PATH"; then
  echo "❌ [tool.poetry] block not found in $TOML_PATH — exiting safely"
  exit 1
fi

if grep -q '^packages\s*=' "$TOML_PATH"; then
  echo "✅ packages already set in $TOML_PATH"
  exit 0
fi

cp "$TOML_PATH" "${TOML_PATH}.bak"

awk -v pkg="$PACKAGE_ENTRY" '
  BEGIN { added = 0 }
  /^\[tool\.poetry\]/ {
    print
    added = 1
    next
  }
  { print }
  END {
    if (added) print pkg;
  }
' "${TOML_PATH}.bak" > "$TOML_PATH"

echo "✅ packages entry inserted into [tool.poetry] block."
