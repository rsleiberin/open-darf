#!/usr/bin/env bash
# Open-DARF Validation Script (Linux/macOS)
# Validates Docker infrastructure and runs verification checks

set -euo pipefail

echo ""
echo "=== Open-DARF Validation ==="
echo "Validating constitutional AI infrastructure"
echo ""

# Check Docker is running
echo "[1/4] Checking Docker daemon..."
if ! docker ps &> /dev/null; then
    echo "❌ ERROR: Docker daemon not running"
    echo "Please start Docker and try again"
    exit 1
fi
echo "✅ Docker daemon is running"

# Check infrastructure services
echo ""
echo "[2/4] Checking infrastructure services..."
CONTAINERS=$(docker ps --format "{{.Names}}" 2>/dev/null || true)
if [ -z "$CONTAINERS" ]; then
    echo "⚠️  No running containers found"
    echo "Run ./install first to deploy infrastructure"
    exit 1
fi

CONTAINER_COUNT=$(echo "$CONTAINERS" | wc -l)
echo "✅ Found $CONTAINER_COUNT running containers:"
echo "$CONTAINERS" | sed 's/^/  - /'

# Check for TLA+ specifications
echo ""
echo "[3/4] Checking TLA+ specifications..."
TLA_PATH="verification/tla"
if [ -d "$TLA_PATH" ]; then
    SPEC_COUNT=$(find "$TLA_PATH" -name "*.tla" | wc -l)
    echo "✅ Found $SPEC_COUNT TLA+ specifications"
    
    # Check for existing evidence
    EVIDENCE_PATH="evidence/tla/class_a"
    if [ -d "$EVIDENCE_PATH/logs" ]; then
        EVIDENCE_COUNT=$(find "$EVIDENCE_PATH/logs" -name "*.log" | wc -l)
        if [ "$EVIDENCE_COUNT" -gt 0 ]; then
            echo "✅ Found existing verification evidence:"
            echo "  Location: $EVIDENCE_PATH/logs"
            echo "  Files: $EVIDENCE_COUNT verification logs"
        fi
    fi
else
    echo "⚠️  No TLA+ specifications found at $TLA_PATH"
fi

# Service health check
echo ""
echo "[4/4] Running service health checks..."
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

if [ "$UNHEALTHY_COUNT" -gt 0 ]; then
    echo ""
    echo "⚠️  Some services may not be healthy"
    echo "Check logs with: docker compose logs <service-name>"
fi

# Summary
echo ""
echo "=== Validation Summary ==="
echo "Infrastructure Status:"
echo "  - Healthy services: $HEALTHY_COUNT"
if [ "$UNHEALTHY_COUNT" -gt 0 ]; then
    echo "  - Unhealthy services: $UNHEALTHY_COUNT"
fi

echo ""
echo "For detailed logs:"
echo "  docker compose logs"
echo ""
echo "To view specific service logs:"
echo "  docker compose logs <service-name>"

echo ""
echo "=== Validation Complete ==="
exit 0
