#!/usr/bin/env bash
# Validation wrapper that auto-submits evidence
set -euo pipefail

TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RECEIPT_FILE="var/receipts/open-darf/validation_${TIMESTAMP}.json"

mkdir -p var/receipts/open-darf

# Run comprehensive validation and capture receipt
./scripts/internal/comprehensive_validation.sh > "$RECEIPT_FILE"

# Display receipt
echo "Receipt saved to: $RECEIPT_FILE"
cat "$RECEIPT_FILE"

# Auto-submit to evidence directory
if [ -f "scripts/evidence/submit_evidence.sh" ]; then
    ./scripts/evidence/submit_evidence.sh "$RECEIPT_FILE"
fi
