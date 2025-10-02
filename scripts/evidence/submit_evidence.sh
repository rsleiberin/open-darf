#!/usr/bin/env bash
# Anonymous evidence submission after validation
set -euo pipefail

RECEIPT_FILE="${1:-}"
if [ -z "$RECEIPT_FILE" ] || [ ! -f "$RECEIPT_FILE" ]; then
    echo "Usage: $0 <receipt_file>"
    exit 1
fi

TIMESTAMP=$(date -u +%Y%m%d_%H%M%S)
PLATFORM=$(uname -s | tr '[:upper:]' '[:lower:]')
VALIDATOR_ID=$(openssl rand -hex 6)

EVIDENCE_DIR="evidence/validation_receipts"
mkdir -p "$EVIDENCE_DIR"

EVIDENCE_FILE="${EVIDENCE_DIR}/validation_${VALIDATOR_ID}_${PLATFORM}_${TIMESTAMP}.json"
cp "$RECEIPT_FILE" "$EVIDENCE_FILE"

echo "Evidence submitted anonymously"
echo "Validator ID: $VALIDATOR_ID (random, not stored)"
echo "Platform: $PLATFORM"
echo "File: $EVIDENCE_FILE"
