#!/bin/bash

echo "=== Testing YAML Parsing ==="

# Test a few files to see if Python can parse the YAML
for file in docs/decisions/000{2..4}*.md; do
    if [ -f "$file" ]; then
        filename=$(basename "$file")
        echo -n "Testing $filename: "

        # Extract and test YAML
        yaml_content=$(awk '/^---$/{flag=1; next} /^---$/{flag=0} flag' "$file")

        if echo "$yaml_content" | python3 -c "
import yaml
import sys
try:
    data = yaml.safe_load(sys.stdin.read())
    if data is None:
        print('Empty YAML')
        sys.exit(1)
    print('Valid YAML - Found', len(data), 'fields')
    sys.exit(0)
except Exception as e:
    print('Invalid YAML:', str(e))
    sys.exit(1)
" 2>/dev/null; then
            echo "✅ YAML OK"
        else
            echo "❌ YAML FAILED"
            echo "YAML content:"
            echo "$yaml_content" | head -5
            echo "---"
        fi
    fi
done
