#!/usr/bin/env bash
# Open-DARF Installation Script (Linux/macOS)
# Deploys Docker infrastructure for constitutional AI validation

set -euo pipefail

echo ""
echo "=== Open-DARF Installation ==="
echo "Deploying Docker infrastructure for constitutional AI validation"
echo ""

# Check Docker availability
echo "[1/5] Checking Docker..."
if ! command -v docker &> /dev/null; then
    echo "❌ ERROR: Docker not found"
    echo "Please install Docker:"
    echo "  Linux: https://docs.docker.com/engine/install/"
    echo "  macOS: https://docs.docker.com/desktop/mac/install/"
    exit 1
fi

DOCKER_VERSION=$(docker --version)
echo "✅ Docker found: $DOCKER_VERSION"

# Check Docker is running
echo ""
echo "[2/5] Checking Docker daemon..."
if ! docker ps &> /dev/null; then
    echo "❌ ERROR: Docker daemon not running"
    echo "Please start Docker and try again"
    exit 1
fi
echo "✅ Docker daemon is running"

# Check Docker Compose availability
echo ""
echo "[3/5] Checking Docker Compose..."
COMPOSE_CMD=""
if command -v docker-compose &> /dev/null; then
    COMPOSE_CMD="docker-compose"
elif docker compose version &> /dev/null; then
    COMPOSE_CMD="docker compose"
fi

if [ -z "$COMPOSE_CMD" ]; then
    echo "❌ ERROR: Docker Compose not available"
    echo "Please install Docker Compose or update Docker"
    exit 1
fi

echo "✅ Docker Compose available: $COMPOSE_CMD"

# Check system resources
echo ""
echo "[4/5] Checking system resources..."
if command -v free &> /dev/null; then
    TOTAL_RAM=$(free -g | awk '/^Mem:/{print $2}')
    if [ "$TOTAL_RAM" -lt 8 ]; then
        echo "⚠️  WARNING: Only ${TOTAL_RAM}GB RAM detected. 8GB+ recommended"
    else
        echo "✅ RAM: ${TOTAL_RAM}GB"
    fi
fi

if command -v df &> /dev/null; then
    FREE_DISK=$(df -BG . | awk 'NR==2 {print $4}' | sed 's/G//')
    if [ "$FREE_DISK" -lt 15 ]; then
        echo "⚠️  WARNING: Only ${FREE_DISK}GB disk space free. 15GB+ recommended"
    else
        echo "✅ Disk: ${FREE_DISK}GB free"
    fi
fi

# Check .env file
if [ ! -f .env ]; then
    if [ -f .env.sample ]; then
        echo ""
        echo "ℹ️  Creating .env from .env.sample"
        cp .env.sample .env
    else
        echo "⚠️  WARNING: No .env or .env.sample found"
    fi
fi

# Deploy infrastructure
echo ""
echo "[5/5] Deploying infrastructure..."
echo "This may take several minutes on first run (downloading images)..."

if ! $COMPOSE_CMD up -d; then
    echo ""
    echo "❌ ERROR: Deployment failed"
    echo "Check logs with: $COMPOSE_CMD logs"
    exit 1
fi

echo ""
echo "✅ Infrastructure deployed successfully!"
echo ""
echo "Services are starting up. You can check status with:"
echo "  docker ps"
echo ""
echo "To validate the system, run:"
echo "  ./validate"
echo ""
echo "To remove all infrastructure:"
echo "  ./cleanup"

echo ""
echo "=== Installation Complete ==="
exit 0
