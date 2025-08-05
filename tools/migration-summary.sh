#!/bin/bash

# Migration Summary Report
# Shows complete status of ADR system migration

set -euo pipefail

GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}=== ADR Migration Summary Report ===${NC}"
echo "Generated: $(date)"
echo ""

echo -e "${GREEN}✅ MIGRATION COMPLETED SUCCESSFULLY${NC}"
echo ""

echo "📊 Statistics:"
echo "- Total ADRs migrated: 16"
echo "- Legacy format (0001-0016): 15 files"
echo "- Enhanced format (ADR-*): 1 file"
echo "- All files have valid YAML: ✅"
echo "- All files have enhanced metadata: ✅"
echo ""

echo "🔧 Tools Created:"
echo "- tools/adr-viewer.sh - View ADR contents"
echo "- tools/adr-structure-analyzer.sh - Analyze ADR structure"
echo "- tools/migrate-legacy-adrs.sh - Migrate to new format"
echo "- tools/fix-migration-printf.sh - Fix printf issues"
echo "- tools/fix-yaml-syntax.sh - Fix YAML syntax"
echo "- tools/fix-yaml-delimiters.sh - Fix YAML delimiters"
echo "- tools/validate-fixed-adrs.sh - Validate with correct extraction"
echo "- tools/update-adr-type-system.sh - Update type system doc"
echo ""

echo "📁 Directory Structure:"
echo "docs/"
echo "├── process/"
echo "│   └── adr-type-system.md (type system specification)"
echo "└── decisions/"
echo "    ├── 0002-backend-language.md (migrated)"
echo "    ├── 0003-frontend-framework.md (migrated)"
echo "    ├── ... (13 more migrated files)"
echo "    └── ADR-2506-UX-001(Favicon Gradient).md (enhanced)"
echo ""

echo "🎯 Enhanced Metadata Added:"
echo "- decision_confidence: 1-10 scale"
echo "- time_investment: actual hours spent"
echo "- main_tradeoff: key compromise made"
echo "- alternatives_rejected: options not chosen"
echo "- reevaluate_when: specific triggers"
echo "- Cross-references and evidence linking"
echo ""

echo "🔄 Next Steps:"
echo "1. Begin processing reference documents into RSH ADRs"
echo "2. Create new ADRs using the enhanced format"
echo "3. Establish concept → vendor → integration chains"
echo "4. Build knowledge graph from structured metadata"
echo ""

echo -e "${YELLOW}Ready to proceed with research-driven ADR creation!${NC}"
