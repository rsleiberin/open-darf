#!/usr/bin/env bash
# Open-DARF Cleanup Script (Linux/macOS)
# Removes all Docker infrastructure for Open-DARF

set -euo pipefail

KEEP_VOLUMES=false
if [ "${1:-}" = "--keep-volumes" ] || [ "${1:-}" = "-k" ]; then
    KEEP_VOLUMES=true
fi

echo ""
echo "=== Open-DARF Cleanup ==="
echo "Removing Docker infrastructure"
echo ""

# Check Docker is running
echo "[1/3] Checking Docker daemon..."
if ! docker ps &> /dev/null; then
    echo "❌ ERROR: Docker daemon not running"
    echo "Please start Docker and try again"
    exit 1
fi
echo "✅ Docker daemon is running"

# Determine compose command
COMPOSE_CMD=""
if command -v docker-compose &> /dev/null; then
    COMPOSE_CMD="docker-compose"
elif docker compose version &> /dev/null; then
    COMPOSE_CMD="docker compose"
fi

if [ -z "$COMPOSE_CMD" ]; then
    echo "⚠️  WARNING: Docker Compose not found"
    echo "Attempting manual cleanup..."
fi

# Stop and remove containers
echo ""
echo "[2/3] Stopping and removing containers..."

if [ -n "$COMPOSE_CMD" ]; then
    if [ "$KEEP_VOLUMES" = true ]; then
        echo "ℹ️  Keeping data volumes (use without --keep-volumes to remove)"
        $COMPOSE_CMD down
    else
        echo "⚠️  Removing data volumes (all data will be lost)"
        $COMPOSE_CMD down -v
    fi
    
    if [ $? -eq 0 ]; then
        echo "✅ Containers and networks removed"
    else
        echo "⚠️  Compose cleanup failed, trying manual cleanup"
    fi
fi

# Verify cleanup
echo ""
echo "[3/3] Verifying cleanup..."

REMAINING_CONTAINERS=$(docker ps -a --format "{{.Names}}" | grep -i darf || true)
if [ -n "$REMAINING_CONTAINERS" ]; then
    echo "⚠️  Some DARF containers still exist:"
    echo "$REMAINING_CONTAINERS" | sed 's/^/  - /'
    echo ""
    echo "Manually remove with:"
    echo "  docker rm -f <container-name>"
else
    echo "✅ No DARF containers remaining"
fi

REMAINING_NETWORKS=$(docker network ls --format "{{.Name}}" | grep -i darf || true)
if [ -n "$REMAINING_NETWORKS" ]; then
    echo "⚠️  Some DARF networks still exist:"
    echo "$REMAINING_NETWORKS" | sed 's/^/  - /'
    echo ""
    echo "Manually remove with:"
    echo "  docker network rm <network-name>"
else
    echo "✅ No DARF networks remaining"
fi

if [ "$KEEP_VOLUMES" = false ]; then
    REMAINING_VOLUMES=$(docker volume ls --format "{{.Name}}" | grep -i darf || true)
    if [ -n "$REMAINING_VOLUMES" ]; then
        echo "⚠️  Some DARF volumes still exist:"
        echo "$REMAINING_VOLUMES" | sed 's/^/  - /'
        echo ""
        echo "Manually remove with:"
        echo "  docker volume rm <volume-name>"
    else
        echo "✅ No DARF volumes remaining"
    fi
fi

echo ""
echo "=== Cleanup Complete ==="
echo "To reinstall, run: ./install"
exit 0
