#!/bin/bash

set -euo pipefail

echo "=== Diagnosing YAML Issues ==="

# Check the first few migrated files for YAML structure
for file in docs/decisions/000{2..5}*.md; do
    if [ -f "$file" ]; then
        echo "=== $(basename "$file") ==="
        echo "First 20 lines:"
        head -20 "$file"
        echo ""
        echo "YAML extraction test:"
        awk '/^---$/{flag=1; next} /^---$/{flag=0} flag' "$file" | head -10
        echo ""
        echo "=========================="
        echo ""
    fi
done
