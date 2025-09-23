#!/bin/bash

# ADR Structure Analyzer
# Analyzes the current structure of ADRs to help with migration planning

ADR_DIR="docs/decisions"
ANALYSIS_FILE="adr-structure-analysis.txt"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo "=== ADR Structure Analyzer ==="
echo "Analyzing ADR structures in: $ADR_DIR"
echo ""

# Check if directory exists
if [ ! -d "$ADR_DIR" ]; then
    echo -e "${RED}Error: Directory $ADR_DIR not found${NC}"
    exit 1
fi

# Clear analysis file
> "$ANALYSIS_FILE"

echo "ADR STRUCTURE ANALYSIS - $(date)" >> "$ANALYSIS_FILE"
echo "==============================================" >> "$ANALYSIS_FILE"
echo "" >> "$ANALYSIS_FILE"

# Analyze each ADR
for adr_file in "$ADR_DIR"/*.md; do
    if [ ! -f "$adr_file" ]; then
        echo -e "${YELLOW}No ADR files found${NC}"
        exit 0
    fi

    filename=$(basename "$adr_file")
    echo -e "${GREEN}Analyzing: $filename${NC}"

    # Extract key structural elements
    echo "FILE: $filename" >> "$ANALYSIS_FILE"
    echo "---" >> "$ANALYSIS_FILE"

    # Check for YAML front matter
    if head -1 "$adr_file" | grep -q "^---"; then
        echo "✓ Has YAML front matter" >> "$ANALYSIS_FILE"
        # Extract YAML fields
        awk '/^---$/{flag=1; next} /^---$/{flag=0} flag' "$adr_file" >> "$ANALYSIS_FILE"
    else
        echo "✗ No YAML front matter detected" >> "$ANALYSIS_FILE"

        # Look for title in first few lines
        title_line=$(head -5 "$adr_file" | grep -E "^#+ " | head -1)
        if [ ! -z "$title_line" ]; then
            echo "Title found: $title_line" >> "$ANALYSIS_FILE"
        fi
    fi

    # Check for common ADR sections
    echo "" >> "$ANALYSIS_FILE"
    echo "Sections detected:" >> "$ANALYSIS_FILE"

    grep -i "^#+ *status" "$adr_file" && echo "✓ Status section" >> "$ANALYSIS_FILE"
    grep -i "^#+ *context" "$adr_file" && echo "✓ Context section" >> "$ANALYSIS_FILE"
    grep -i "^#+ *decision" "$adr_file" && echo "✓ Decision section" >> "$ANALYSIS_FILE"
    grep -i "^#+ *rationale" "$adr_file" && echo "✓ Rationale section" >> "$ANALYSIS_FILE"
    grep -i "^#+ *consequences" "$adr_file" && echo "✓ Consequences section" >> "$ANALYSIS_FILE"
    grep -i "^#+ *alternatives" "$adr_file" && echo "✓ Alternatives section" >> "$ANALYSIS_FILE"

    # Count lines and words
    line_count=$(wc -l < "$adr_file")
    word_count=$(wc -w < "$adr_file")
    echo "Lines: $line_count, Words: $word_count" >> "$ANALYSIS_FILE"

    echo "" >> "$ANALYSIS_FILE"
    echo "===========================================" >> "$ANALYSIS_FILE"
    echo "" >> "$ANALYSIS_FILE"
done

# Summary
echo "" >> "$ANALYSIS_FILE"
echo "MIGRATION RECOMMENDATIONS" >> "$ANALYSIS_FILE"
echo "==========================" >> "$ANALYSIS_FILE"
echo "" >> "$ANALYSIS_FILE"

# Count files with/without YAML
yaml_count=0
no_yaml_count=0

for adr_file in "$ADR_DIR"/*.md; do
    if head -1 "$adr_file" | grep -q "^---"; then
        yaml_count=$((yaml_count + 1))
    else
        no_yaml_count=$((no_yaml_count + 1))
    fi
done

echo "Files with YAML front matter: $yaml_count" >> "$ANALYSIS_FILE"
echo "Files without YAML front matter: $no_yaml_count" >> "$ANALYSIS_FILE"
echo "" >> "$ANALYSIS_FILE"

if [ $no_yaml_count -gt 0 ]; then
    echo "PRIORITY: Add YAML front matter to files without it" >> "$ANALYSIS_FILE"
fi

echo "Next steps:" >> "$ANALYSIS_FILE"
echo "1. Review this analysis" >> "$ANALYSIS_FILE"
echo "2. Use tools/adr-viewer.sh to get full contents" >> "$ANALYSIS_FILE"
echo "3. Update each ADR with new type system metadata" >> "$ANALYSIS_FILE"

echo ""
echo -e "${BLUE}Analysis complete!${NC}"
echo "Results saved to: $ANALYSIS_FILE"
echo ""
echo -e "${YELLOW}Usage workflow:${NC}"
echo "1. Run this script: ./tools/adr-structure-analyzer.sh"
echo "2. Run content viewer: ./tools/adr-viewer.sh"
echo "3. Review both output files"
echo "4. Share individual ADR contents with Claude for updating"
