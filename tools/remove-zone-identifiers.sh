#!/bin/bash
set -euo pipefail

echo "  Scanning and removing .Zone.Identifier files from docs/..."

count=0
while IFS= read -r file; do
    if [[ -f "$file" ]]; then
        rm -f "$file"
        echo "🗑️ Removed: $file"
        ((count++))
    fi
done < <(find docs/ -type f -name "*.Zone.Identifier")

if [[ $count -eq 0 ]]; then
    echo "✅ No .Zone.Identifier files found."
else
    echo "✅ Deleted $count .Zone.Identifier file(s)."
fi

