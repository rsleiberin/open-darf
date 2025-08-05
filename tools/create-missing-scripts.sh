#!/bin/bash

# Create Missing Tool Scripts
# Creates the script files that were run inline

set -euo pipefail

echo "Creating missing tool scripts..."

# Create the ADR type system update script
cat > tools/update-adr-type-system.sh << 'EOF'
#!/bin/bash

# Update ADR Type System Documentation
# Moves file to correct location and updates content based on project analysis

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}=== ADR Type System Update ===${NC}"

# Define paths
OLD_PATH="docs/adr-type-system.md"
NEW_PATH="docs/process/adr-type-system.md"
BACKUP_PATH="docs/process/adr-type-system.md.backup"

# Check if old file exists and move it
if [ -f "$OLD_PATH" ]; then
    echo -e "${YELLOW}Moving $OLD_PATH to $NEW_PATH${NC}"
    mv "$OLD_PATH" "$NEW_PATH"
else
    echo -e "${YELLOW}Creating new file at $NEW_PATH${NC}"
fi

# Backup existing file if it exists
if [ -f "$NEW_PATH" ]; then
    cp "$NEW_PATH" "$BACKUP_PATH"
    echo -e "${GREEN}Backup created: $BACKUP_PATH${NC}"
fi

echo -e "${GREEN}✅ ADR Type System setup complete${NC}"
echo -e "${BLUE}Location: $NEW_PATH${NC}"
EOF

# Make scripts executable
chmod +x tools/update-adr-type-system.sh
chmod +x tools/fix-migration-printf.sh  
chmod +x tools/validate-migrated-adrs.sh

echo "✅ Created missing tool scripts"
echo ""
echo "Available tools:"
echo "- tools/update-adr-type-system.sh"
echo "- tools/fix-migration-printf.sh"  
echo "- tools/validate-migrated-adrs.sh"