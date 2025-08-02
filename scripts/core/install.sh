#!/usr/bin/env bash
set -euo pipefail

echo "=== Open-DARF Installation ==="
echo "Deploying Docker infrastructure for constitutional AI validation"
echo ""

echo "[1/5] Checking Docker..."
if ! command -v docker &> /dev/null; then
    echo "❌ ERROR: Docker not found"
    echo "Please install Docker: https://docs.docker.com/get-docker/"
    exit 1
fi
DOCKER_VERSION=$(docker --version)
echo "✅ Docker found: $DOCKER_VERSION"
echo ""

echo "[2/5] Checking Docker daemon..."
if ! docker ps &> /dev/null; then
    echo "❌ ERROR: Docker daemon not running"
    echo "Please start Docker Desktop and try again"
    exit 1
fi
echo "✅ Docker daemon is running"
echo ""

echo "[3/5] Checking Docker Compose..."
COMPOSE_CMD=""
if docker compose version &> /dev/null; then
    COMPOSE_CMD="docker compose"
    echo "✅ Docker Compose available: docker compose (plugin)"
elif command -v docker-compose &> /dev/null; then
    COMPOSE_CMD="docker-compose"
    echo "✅ Docker Compose available: docker-compose (standalone)"
fi

if [ -z "$COMPOSE_CMD" ]; then
    echo "❌ ERROR: Docker Compose not found"
    echo "Install: https://docs.docker.com/compose/install/"
    exit 1
fi
echo ""

echo "[4/5] Checking system resources..."
TOTAL_RAM=$(free -g | awk '/^Mem:/{print $2}')
FREE_DISK=$(df -BG . | awk 'NR==2{print $4}' | sed 's/G//')

if [ "$TOTAL_RAM" -lt 4 ]; then
    echo "⚠️  WARNING: Only ${TOTAL_RAM}GB RAM. 8GB+ recommended"
else
    echo "✅ RAM: ${TOTAL_RAM}GB"
fi

if [ "$FREE_DISK" -lt 15 ]; then
    echo "⚠️  WARNING: Only ${FREE_DISK}GB free. 15GB+ recommended"
else
    echo "✅ Disk: ${FREE_DISK}GB free"
fi

if [ ! -f ".env" ]; then
    if [ -f ".env.sample" ]; then
        echo "ℹ️  Creating .env from .env.sample"
        cp .env.sample .env
    fi
fi
echo ""

echo "[5/5] Deploying infrastructure..."
echo "This may take several minutes on first run (downloading images)..."
if ! $COMPOSE_CMD up -d; then
    echo "❌ ERROR: Deployment failed"
    echo "Check logs with: $COMPOSE_CMD logs"
    exit 1
fi

echo ""
echo "✅ Infrastructure deployed successfully!"
echo ""
echo "Next steps:"
echo "  Check status: docker ps"
echo "  Run validation: ./validate"
echo "  Cleanup: ./cleanup"
echo ""
echo "=== Installation Complete ==="
exit 0
