#!/bin/bash

# Rename ADRs to New Format
# Renames all legacy ADRs to proper ADR-YYMM-TYPE-NNN format

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}=== Renaming ADRs to New Format ===${NC}"

ADR_DIR="docs/decisions"
RENAME_LOG="adr-rename-$(date +%Y%m%d-%H%M%S).log"

echo "ADR Rename Log - $(date)" > "$RENAME_LOG"
echo "===========================" >> "$RENAME_LOG"

renamed_count=0

# Process each legacy ADR file (skip the one that's already renamed)
for adr_file in "$ADR_DIR"/[0-9]*.md; do
    if [ -f "$adr_file" ]; then
        filename=$(basename "$adr_file")
        echo -e "${YELLOW}Processing: $filename${NC}"
        
        # Extract new ID from the file content
        new_id=$(sed -n '/^---$/,/^---$/p' "$adr_file" | sed '1d;$d' | grep "^id:" | cut -d: -f2 | tr -d ' ')
        
        if [ -n "$new_id" ]; then
            # Create new filename from ID
            new_filename="${new_id}.md"
            new_filepath="$ADR_DIR/$new_filename"
            
            echo "  Renaming to: $new_filename"
            echo "Renamed: $filename -> $new_filename" >> "$RENAME_LOG"
            
            # Rename the file
            mv "$adr_file" "$new_filepath"
            
            renamed_count=$((renamed_count + 1))
        else
            echo "  ❌ Could not extract ID from $filename"
            echo "ERROR: Could not extract ID from $filename" >> "$RENAME_LOG"
        fi
    fi
done

echo ""
echo -e "${GREEN}✅ Renamed $renamed_count ADR files${NC}"
echo -e "${YELLOW}📋 Rename log: $RENAME_LOG${NC}"

echo ""
echo "New file listing:"
ls -1 "$ADR_DIR"/ADR-*.md | head -5
echo "..."
echo "Total ADR files: $(ls -1 "$ADR_DIR"/ADR-*.md | wc -l)"
