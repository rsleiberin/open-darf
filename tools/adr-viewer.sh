#!/bin/bash

# ADR Content Viewer Script
# Displays contents of all ADRs in the decisions directory

ADR_DIR="docs/decisions"
OUTPUT_FILE="adr-contents-review.txt"

# Colors for better readability
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "=== ADR Content Viewer ===" 
echo "Scanning directory: $ADR_DIR"
echo "Output will be saved to: $OUTPUT_FILE"
echo ""

# Check if directory exists
if [ ! -d "$ADR_DIR" ]; then
    echo -e "${RED}Error: Directory $ADR_DIR not found${NC}"
    exit 1
fi

# Clear the output file
> "$OUTPUT_FILE"

# Header for output file
echo "ADR CONTENTS REVIEW - $(date)" >> "$OUTPUT_FILE"
echo "=========================================" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Counter for ADRs found
adr_count=0

# Process each ADR file
for adr_file in "$ADR_DIR"/*.md; do
    # Check if files exist (handles case where no .md files found)
    if [ ! -f "$adr_file" ]; then
        echo -e "${YELLOW}No ADR files found in $ADR_DIR${NC}"
        exit 0
    fi
    
    filename=$(basename "$adr_file")
    adr_count=$((adr_count + 1))
    
    echo -e "${GREEN}Processing: $filename${NC}"
    
    # Add to output file
    echo "FILE: $filename" >> "$OUTPUT_FILE"
    echo "==========================================" >> "$OUTPUT_FILE"
    cat "$adr_file" >> "$OUTPUT_FILE"
    echo "" >> "$OUTPUT_FILE"
    echo "===========================================" >> "$OUTPUT_FILE"
    echo "" >> "$OUTPUT_FILE"
done

echo ""
echo -e "${BLUE}Summary:${NC}"
echo "- Found $adr_count ADR files"
echo "- Contents saved to: $OUTPUT_FILE"
echo ""
echo -e "${YELLOW}Next steps:${NC}"
echo "1. Review the contents in $OUTPUT_FILE"
echo "2. Copy and paste individual ADR contents to Claude for structure updates"
echo "3. Use the updated ADR templates for consistent formatting"

# Display quick summary of files found
echo ""
echo -e "${BLUE}Files processed:${NC}"
ls -1 "$ADR_DIR"/*.md 2>/dev/null | while read file; do
    echo "  - $(basename "$file")"
done