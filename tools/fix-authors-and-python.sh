#!/bin/bash
set -euo pipefail

TOML="pyproject.toml"
BACKUP="${TOML}.authors-python-fix.bak"
TMP="${TOML}.tmp"

echo "🧪 Backing up $TOML → $BACKUP"
cp "$TOML" "$BACKUP"

awk '
  BEGIN { in_poetry = 0 }
  /^\[tool\.poetry\]/ { in_poetry = 1; print; next }
  /^\[/ { in_poetry = 0 }

  in_poetry && /^\s*authors\s*=/ {
    print "authors = [\"darf\"]"
    next
  }

  in_poetry && /^\s*python\s*=/ {
    python_line = $0
    sub(/^\s*python\s*=\s*/, "", python_line)
    python_val = python_line
    next
  }

  { print }

  END {
    if (python_val != "") {
      print "[tool.poetry.dependencies]"
      print "python = " python_val
    }
  }
' "$BACKUP" > "$TMP"

mv "$TMP" "$TOML"
echo "✅ Fixed authors format and moved python to [tool.poetry.dependencies]"
