#!/bin/bash

echo "=== Debug Validation Logic ==="

file="docs/decisions/0002-backend-language.md"
echo "Testing file: $file"

echo ""
echo "1. YAML Front Matter Check:"
if head -1 "$file" | grep -q "^---"; then
    echo "✅ Has YAML front matter"
else
    echo "❌ No YAML front matter"
fi

echo ""
echo "2. Enhanced Metadata Check:"
if grep -q "decision_confidence:" "$file" && grep -q "time_investment:" "$file"; then
    echo "✅ Has enhanced metadata"
else
    echo "❌ Missing enhanced metadata"
fi

echo ""
echo "3. YAML Syntax Check:"
yaml_content=$(awk '/^---$/{flag=1; next} /^---$/{flag=0} flag' "$file")
if echo "$yaml_content" | python3 -c "
import yaml
import sys
try:
    yaml.safe_load(sys.stdin.read())
    print('✅ Valid YAML syntax')
except Exception as e:
    print('❌ Invalid YAML:', e)
    sys.exit(1)
" 2>/dev/null; then
    echo "YAML parsing succeeded"
else
    echo "YAML parsing failed"
fi
