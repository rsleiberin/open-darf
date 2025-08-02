#!/usr/bin/env bash
# Open-DARF Comprehensive Validation
set -euo pipefail

SKIP_CONSTITUTIONAL=false
if [[ "${1:-}" == "--skip-constitutional" ]]; then
    SKIP_CONSTITUTIONAL=true
fi

echo ""
echo "=== Open-DARF Validation ==="
echo "Comprehensive: Document Ingestion + Constitutional Validation"
echo ""

# [1/3] Check Docker daemon
echo "[1/3] Checking Docker infrastructure..."
if ! docker ps &> /dev/null; then
    echo "❌ ERROR: Docker daemon not running"
    exit 1
fi

CONTAINERS=$(docker ps --format "{{.Names}}" 2>/dev/null || true)
CONTAINER_COUNT=$(echo "$CONTAINERS" | wc -l)
echo "✅ Found $CONTAINER_COUNT running containers"

# [2/3] Create receipt directory
echo ""
echo "[2/3] Preparing receipt directory..."
mkdir -p var/receipts/open-darf
echo "✅ Receipt directory ready"

# [3/3] Run comprehensive validation
if [ "$SKIP_CONSTITUTIONAL" = false ]; then
    echo ""
    echo "[3/3] Running comprehensive validation..."
    TIMESTAMP=$(date -u +"%Y%m%d_%H%M%S")
    RECEIPT_PATH="var/receipts/open-darf/validation_${TIMESTAMP}.json"
    
    if ./scripts/internal/comprehensive_validation.sh 2>/tmp/validate_stderr.log 1>"$RECEIPT_PATH"; then
        echo "✅ Comprehensive validation complete"
        
        if command -v jq &> /dev/null; then
            echo ""
            echo "Results:"
            jq -r '"  Test: " + .test_scenario' "$RECEIPT_PATH"
            jq -r '"  Document SHA256: " + .document_ingestion.sha256_hash[0:16] + "..."' "$RECEIPT_PATH"
            jq -r '"  Validations: " + (.constitutional_validations | length | tostring) + " rules tested"' "$RECEIPT_PATH"
            jq -r '"  Total time: " + (.pipeline_performance.total_end_to_end_ms | tostring) + "ms"' "$RECEIPT_PATH"
            jq -r '"  Database I/O: " + (.pipeline_performance.percentage_breakdown.database_io | tostring) + "%"' "$RECEIPT_PATH"
        fi
        
        echo ""
        echo "  Receipt: $RECEIPT_PATH"
    else
        echo "⚠️  Validation encountered an error"
        cat /tmp/validate_stderr.log
        exit 1
    fi
else
    echo ""
    echo "[3/3] Skipping validation (--skip-constitutional)"
fi

echo ""
echo "=== Validation Complete ==="
exit 0
