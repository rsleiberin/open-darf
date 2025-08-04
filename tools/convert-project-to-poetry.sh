#!/bin/bash
set -euo pipefail

TOML="pyproject.toml"
BACKUP="${TOML}.backup-before-poetry"

if ! grep -q '^\[project\]' "$TOML"; then
  echo "❌ [project] block not found — nothing to convert."
  exit 1
fi

echo "🧪 Backing up $TOML → $BACKUP"
cp "$TOML" "$BACKUP"

awk '
  BEGIN { in_project=0 }
  /^\[project\]/ { print "[tool.poetry]"; in_project=1; next }
  /^\[/ { in_project=0 }
  {
    if (in_project) gsub(/name =/, "name =");
    if (in_project) gsub(/version =/, "version =");
    if (in_project) gsub(/description =/, "description =");
    if (in_project) gsub(/readme =/, "readme =");
    if (in_project) gsub(/requires-python =/, "python =");
    if (in_project) gsub(/authors =/, "authors =");
    if (in_project) gsub(/dependencies =/, "dependencies =");
    print
  }
' "$BACKUP" > "$TOML"

echo "✅ Converted [project] → [tool.poetry]"
