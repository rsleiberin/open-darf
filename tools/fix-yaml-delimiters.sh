#!/bin/bash

# Fix Missing YAML Closing Delimiters
# Adds proper closing --- to YAML front matter

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}=== Fixing YAML Delimiters ===${NC}"

ADR_DIR="docs/decisions"
FIX_LOG="yaml-delimiters-fix-$(date +%Y%m%d-%H%M%S).log"

echo "YAML Delimiters Fix Log - $(date)" > "$FIX_LOG"
echo "===================================" >> "$FIX_LOG"

fixed_count=0

for adr_file in "$ADR_DIR"/*.md; do
    if [ -f "$adr_file" ]; then
        filename=$(basename "$adr_file")
        echo -e "${YELLOW}Processing: $filename${NC}"
        
        # Check if file has YAML front matter but missing closing delimiter
        if head -1 "$adr_file" | grep -q "^---"; then
            # Count the number of --- delimiters
            delimiter_count=$(grep -c "^---$" "$adr_file")
            
            if [ "$delimiter_count" -eq 1 ]; then
                echo "  Fixing missing closing delimiter"
                
                # Create temporary file with proper YAML structure
                {
                    in_yaml=true
                    first_delimiter_passed=false
                    
                    while IFS= read -r line; do
                        if [ "$line" = "---" ] && [ "$first_delimiter_passed" = "false" ]; then
                            echo "$line"
                            first_delimiter_passed=true
                        elif [ "$first_delimiter_passed" = "true" ] && [ "$in_yaml" = "true" ]; then
                            # Check if this line looks like markdown content
                            if [[ "$line" =~ ^#[[:space:]] ]] || [[ "$line" =~ ^\|.*\| ]] || [ -z "$line" ]; then
                                # This is the start of markdown content, close YAML
                                echo "---"
                                echo ""
                                echo "$line"
                                in_yaml=false
                            else
                                # Still YAML content
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
                echo "✅ Fixed YAML delimiters in $filename" >> "$FIX_LOG"
            else
                echo "  Already has proper delimiters"
            fi
        fi
    fi
done

echo ""
echo -e "${GREEN}✅ Fixed YAML delimiters in $fixed_count files${NC}"
echo -e "${YELLOW}📋 Fix log: $FIX_LOG${NC}"
