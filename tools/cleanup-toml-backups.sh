#!/bin/bash
set -euo pipefail

echo "🧹 Cleaning up old pyproject.toml backups..."

find . -maxdepth 1 -type f \
  \( -name 'pyproject.toml.*.bak' -o -name 'pyproject.toml.conflict-*' -o -name 'pyproject.toml.bak' \) \
  -exec bash -c 'echo "🗑️  Removing: $1"; rm "$1"' _ {} \;

echo "✅ Cleanup complete."
