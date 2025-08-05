#!/bin/bash

# Fix Printf Issue in Migrated ADRs
# Corrects the octal number formatting issue from the migration

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}=== Fixing Printf Issues in Migrated ADRs ===${NC}"

ADR_DIR="docs/decisions"
FIX_LOG="printf-fix-$(date +%Y%m%d-%H%M%S).log"

echo "Printf Fix Log - $(date)" > "$FIX_LOG"
echo "================================" >> "$FIX_LOG"

fixed_count=0

# Process each migrated ADR file
for adr_file in "$ADR_DIR"/ADR-*.md; do
    if [ -f "$adr_file" ]; then
        filename=$(basename "$adr_file")
        echo -e "${YELLOW}Checking: $filename${NC}"
        
        # Check if file has invalid legacy_id formatting
        if grep -q "legacy_id: 00[0-9][0-9]" "$adr_file"; then
            echo -e "${GREEN}Fixing: $filename${NC}"
            echo "Fixing: $filename" >> "$FIX_LOG"
            
            # Create temporary file with corrected legacy_id
            sed 's/legacy_id: 00\([0-9][0-9]\)/legacy_id: \1/' "$adr_file" > "${adr_file}.tmp"
            mv "${adr_file}.tmp" "$adr_file"
            
            fixed_count=$((fixed_count + 1))
            echo "✅ Fixed legacy_id format in $filename" >> "$FIX_LOG"
        fi
    fi
done

echo ""
echo -e "${BLUE}Fix Summary:${NC}"
echo -e "${GREEN}✅ Fixed $fixed_count ADR files${NC}"
echo -e "${YELLOW}📋 Fix log: $FIX_LOG${NC}"

echo ""
echo -e "${YELLOW}Next: Run validation to check results${NC}"
echo "Command: ./tools/validate-migrated-adrs.sh"