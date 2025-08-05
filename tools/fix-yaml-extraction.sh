#!/bin/bash

# Test correct YAML extraction
echo "=== Testing Correct YAML Extraction ==="

file="docs/decisions/0002-backend-language.md"
echo "File: $file"
echo ""

# Correct method: extract content between first and second ---
echo "Correct YAML extraction:"
sed -n '/^---$/,/^---$/p' "$file" | sed '1d;$d'

echo ""
echo "=== Testing YAML parsing ==="
yaml_content=$(sed -n '/^---$/,/^---$/p' "$file" | sed '1d;$d')

if echo "$yaml_content" | python3 -c "
import yaml
import sys
try:
    data = yaml.safe_load(sys.stdin.read())
    print('✅ Valid YAML - Found', len(data), 'fields')
    for key in data.keys():
        print('  -', key)
except Exception as e:
    print('❌ Invalid YAML:', str(e))
    sys.exit(1)
"; then
    echo "YAML parsing successful!"
else
    echo "YAML parsing failed"
fi
