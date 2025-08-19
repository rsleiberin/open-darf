#!/bin/bash

# Validate Migrated ADRs
# Simplified validation focused on migration issues

set -euo pipefail

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}=== Validating Migrated ADRs ===${NC}"

ADR_DIR="docs/decisions"
VALIDATION_LOG="migration-validation-$(date +%Y%m%d-%H%M%S).log"

echo "Migration Validation Report - $(date)" > "$VALIDATION_LOG"
echo "=====================================" >> "$VALIDATION_LOG"

total_files=0
valid_yaml=0
has_enhanced_metadata=0
needs_fixes=0

# Check each ADR file
for adr_file in "$ADR_DIR"/*.md; do
    if [ -f "$adr_file" ]; then
        filename=$(basename "$adr_file")
        total_files=$((total_files + 1))

        echo -ne "${BLUE}Checking: $filename${NC}"

        file_issues=()

        # Check 1: YAML front matter exists
        if head -1 "$adr_file" | grep -q "^---"; then
            valid_yaml=$((valid_yaml + 1))
        else
            file_issues+=("no_yaml")
        fi

        # Check 2: Has enhanced metadata fields
        if grep -q "decision_confidence:" "$adr_file" && grep -q "time_investment:" "$adr_file"; then
            has_enhanced_metadata=$((has_enhanced_metadata + 1))
        else
            file_issues+=("missing_enhanced_fields")
        fi

        # Check 3: YAML syntax validation (basic)
        if head -1 "$adr_file" | grep -q "^---"; then
            yaml_content=$(awk '/^---$/{flag=1; next} /^---$/{flag=0} flag' "$adr_file")
            if echo "$yaml_content" | python3 -c "
import yaml
import sys
try:
    yaml.safe_load(sys.stdin.read())
except:
    sys.exit(1)
" 2>/dev/null; then
                # YAML is valid
                :
            else
                file_issues+=("invalid_yaml_syntax")
            fi
        fi

        # Report results
        if [ ${#file_issues[@]} -eq 0 ]; then
            echo -e " ${GREEN}✅${NC}"
            echo "✅ $filename: All checks passed" >> "$VALIDATION_LOG"
        else
            echo -e " ${YELLOW}⚠️${NC}"
            echo "⚠️  $filename: Issues: ${file_issues[*]}" >> "$VALIDATION_LOG"
            needs_fixes=$((needs_fixes + 1))
        fi
    fi
done

# Summary
echo ""
echo -e "${BLUE}Validation Summary:${NC}"
echo -e "${GREEN}Total files checked: $total_files${NC}"
echo -e "${GREEN}Files with valid YAML: $valid_yaml${NC}"
echo -e "${GREEN}Files with enhanced metadata: $has_enhanced_metadata${NC}"
echo -e "${YELLOW}Files needing fixes: $needs_fixes${NC}"

echo ""
echo "Detailed results in: $VALIDATION_LOG"

# Show sample of first migrated file
echo ""
echo -e "${YELLOW}Sample of migrated ADR:${NC}"
echo "========================"
first_adr=$(find "$ADR_DIR" -name "ADR-*.md" | head -1)
if [ -f "$first_adr" ]; then
    echo "File: $(basename "$first_adr")"
    echo "First 15 lines:"
    head -15 "$first_adr"
else
    echo "No ADR-*.md files found"
fi
