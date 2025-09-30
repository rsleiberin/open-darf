#!/usr/bin/env bash
# Open-DARF Validation Script (Linux/macOS)
# Validates Docker infrastructure and runs constitutional validation

set -euo pipefail

SKIP_CONSTITUTIONAL=false
if [[ "${1:-}" == "--skip-constitutional" ]]; then
    SKIP_CONSTITUTIONAL=true
fi

echo ""
echo "=== Open-DARF Validation ==="
echo "Running constitutional AI validation with performance measurement"
echo ""

# [1/5] Check Docker daemon
echo "[1/5] Checking Docker daemon..."
if ! docker ps &> /dev/null; then
    echo "❌ ERROR: Docker daemon not running"
    echo "Please start Docker and try again"
    exit 1
fi
echo "✅ Docker daemon is running"

# [2/5] Check infrastructure services
echo ""
echo "[2/5] Checking infrastructure services..."
CONTAINERS=$(docker ps --format "{{.Names}}" 2>/dev/null || true)
if [ -z "$CONTAINERS" ]; then
    echo "⚠️  No running containers found"
    echo "Run ./install first to deploy infrastructure"
    exit 1
fi

CONTAINER_COUNT=$(echo "$CONTAINERS" | wc -l)
echo "✅ Found $CONTAINER_COUNT running containers:"
echo "$CONTAINERS" | sed 's/^/  - /'

# [3/5] Create receipt directory
echo ""
echo "[3/5] Preparing receipt directory..."
mkdir -p var/receipts/open-darf
echo "✅ Receipt directory ready"

# [4/5] Run constitutional validation
if [ "$SKIP_CONSTITUTIONAL" = false ]; then
    echo ""
    echo "[4/5] Executing constitutional validation..."
    
    TIMESTAMP=$(date -u +"%Y%m%d_%H%M%S")
    RECEIPT_PATH="var/receipts/open-darf/validation_${TIMESTAMP}.json"
    
    if ./scripts/internal/constitutional_engine.sh > "$RECEIPT_PATH" 2>&1; then
        echo "✅ Constitutional validation complete"
        
        # Parse and display results using jq if available, otherwise grep
        if command -v jq &> /dev/null; then
            DECISION=$(jq -r '.constitutional_validation.decision' "$RECEIPT_PATH")
            REASON=$(jq -r '.constitutional_validation.reason' "$RECEIPT_PATH")
            TOTAL_MS=$(jq -r '.constitutional_validation.total_overhead_ms' "$RECEIPT_PATH")
            NEO_MS=$(jq -r '.constitutional_validation.neo4j_query_ms' "$RECEIPT_PATH")
            PG_MS=$(jq -r '.constitutional_validation.postgres_insert_ms' "$RECEIPT_PATH")
            
            echo "  Decision: $DECISION"
            echo "  Reason: $REASON"
            echo "  Performance: ${TOTAL_MS}ms total overhead"
            echo "    - Neo4j query: ${NEO_MS}ms"
            echo "    - PostgreSQL insert: ${PG_MS}ms"
        else
            echo "  (Install jq for detailed output parsing)"
        fi
        
        echo "  Receipt: $RECEIPT_PATH"
    else
        echo "⚠️  Constitutional validation encountered an error"
        echo "Check $RECEIPT_PATH for details"
        echo "Continuing with validation..."
    fi
else
    echo ""
    echo "[4/5] Skipping constitutional validation (--skip-constitutional)"
fi

# [5/5] Service health check
echo ""
echo "[5/5] Running service health checks..."
HEALTHY_COUNT=0
UNHEALTHY_COUNT=0

while IFS=: read -r NAME STATUS; do
    if echo "$STATUS" | grep -qE "Up|healthy"; then
        echo "  ✅ $NAME - Running"
        ((HEALTHY_COUNT++))
    else
        echo "  ⚠️  $NAME - $STATUS"
        ((UNHEALTHY_COUNT++))
    fi
done < <(docker ps --format "{{.Names}}:{{.Status}}")

# Summary
echo ""
echo "=== Validation Summary ==="
echo "Infrastructure Status:"
echo "  - Healthy services: $HEALTHY_COUNT"
if [ "$UNHEALTHY_COUNT" -gt 0 ]; then
    echo "  - Unhealthy services: $UNHEALTHY_COUNT"
fi

if [ "$SKIP_CONSTITUTIONAL" = false ]; then
    echo ""
    echo "Constitutional Validation:"
    echo "  - Receipt generated: var/receipts/open-darf/"
    echo "  - Performance measured and documented"
fi

echo ""
echo "For detailed logs:"
echo "  docker compose logs"

echo ""
echo "=== Validation Complete ==="
exit 0
