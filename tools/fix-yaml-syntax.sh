#!/bin/bash

# Fix YAML Syntax Issues in Migrated ADRs
# Removes YAML comments that are causing parsing errors

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}=== Fixing YAML Syntax Issues ===${NC}"

ADR_DIR="docs/decisions"
FIX_LOG="yaml-fix-$(date +%Y%m%d-%H%M%S).log"

echo "YAML Fix Log - $(date)" > "$FIX_LOG"
echo "=========================" >> "$FIX_LOG"

fixed_count=0

for adr_file in "$ADR_DIR"/*.md; do
    if [ -f "$adr_file" ]; then
        filename=$(basename "$adr_file")
        echo -e "${YELLOW}Processing: $filename${NC}"
        
        # Create temporary file with fixed YAML
        {
            # Process line by line
            in_yaml=false
            while IFS= read -r line; do
                if [ "$line" = "---" ]; then
                    echo "$line"
                    if [ "$in_yaml" = "false" ]; then
                        in_yaml=true
                    else
                        in_yaml=false
                    fi
                elif [ "$in_yaml" = "true" ]; then
                    # Remove comment lines in YAML front matter
                    if [[ "$line" =~ ^[[:space:]]*# ]]; then
                        # Skip comment lines
                        continue
                    else
                        echo "$line"
                    fi
                else
                    echo "$line"
                fi
            done < "$adr_file"
        } > "${adr_file}.tmp"
        
        # Replace original with fixed version
        mv "${adr_file}.tmp" "$adr_file"
        
        fixed_count=$((fixed_count + 1))
        echo "✅ Fixed YAML in $filename" >> "$FIX_LOG"
    fi
done

echo ""
echo -e "${GREEN}✅ Fixed YAML syntax in $fixed_count files${NC}"
echo -e "${YELLOW}📋 Fix log: $FIX_LOG${NC}"
