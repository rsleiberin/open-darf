#!/bin/bash

# Validate ADRs with Correct YAML Extraction
set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}=== Validating ADRs with Fixed Extraction ===${NC}"

ADR_DIR="docs/decisions"
total_files=0
valid_files=0
failed_files=0

for adr_file in "$ADR_DIR"/*.md; do
    if [ -f "$adr_file" ]; then
        filename=$(basename "$adr_file")
        total_files=$((total_files + 1))

        echo -ne "${BLUE}Validating: $filename${NC}"

        # Check if file has YAML front matter
        if head -1 "$adr_file" | grep -q "^---"; then
            # Extract YAML correctly (between first and second ---)
            yaml_content=$(sed -n '/^---$/,/^---$/p' "$adr_file" | sed '1d;$d')

            # Test YAML parsing
            if echo "$yaml_content" | python3 -c "
import yaml
import sys
try:
    data = yaml.safe_load(sys.stdin.read())
    if data is None:
        sys.exit(1)
except:
    sys.exit(1)
" 2>/dev/null; then
                echo -e " ${GREEN}✅${NC}"
                valid_files=$((valid_files + 1))
            else
                echo -e " ${RED}❌${NC}"
                failed_files=$((failed_files + 1))
            fi
        else
            echo -e " ${YELLOW}⚠️ No YAML${NC}"
        fi
    fi
done

echo ""
echo -e "${BLUE}Validation Results:${NC}"
echo -e "${GREEN}✅ Valid: $valid_files${NC}"
echo -e "${RED}❌ Failed: $failed_files${NC}"
echo -e "${BLUE}📊 Total: $total_files${NC}"

if [ $failed_files -eq 0 ]; then
    echo -e "${GREEN}🎉 All ADRs have valid YAML!${NC}"
else
    echo -e "${YELLOW}⚠️  Some ADRs still have issues${NC}"
fi
