# Linux/macOS Installation Guide

## Prerequisites Check

## Step 1: System Verification

Run this bash command to verify your system meets requirements:

    echo "=== OPEN-DARF SYSTEM CHECK ==="; ready=true; os_name=$(uname -s); os_version=$(uname -r); ram_gb=$(free -g | awk '/^Mem:/{print $2}'); disk_gb=$(df -BG / | awk 'NR==2{print $4}' | sed 's/G//'); docker_ver=$(command -v docker >/dev/null 2>&1 && docker --version || echo ""); podman_ver=$(command -v podman >/dev/null 2>&1 && podman --version || echo ""); if [ -n "$os_name" ]; then echo "✅ OS: $os_name $os_version"; else echo "❌ OS: Unknown"; ready=false; fi; if [ "$ram_gb" -ge 8 ]; then echo "✅ RAM: ${ram_gb}GB"; else echo "❌ RAM: ${ram_gb}GB - Need 8GB+"; ready=false; fi; if [ "${disk_gb}" -ge 15 ]; then echo "✅ Disk: ${disk_gb}GB free"; else echo "❌ Disk: ${disk_gb}GB free - Need 15GB+"; ready=false; fi; if [ -z "$docker_ver" ] && [ -z "$podman_ver" ]; then echo "❌ Container Platform: Not found"; echo "  Install Docker: https://docs.docker.com/engine/install/"; echo "  Install Podman: https://podman.io/getting-started/installation"; ready=false; else [ -n "$docker_ver" ] && echo "✅ Docker: $docker_ver"; [ -n "$podman_ver" ] && echo "✅ Podman: $podman_ver"; fi; echo ""; echo "=== RESULT ==="; if [ "$ready" = true ]; then echo "✅ YOUR SYSTEM IS READY FOR OPEN-DARF!"; echo "Next step: Proceed to installation"; else echo "❌ SYSTEM REQUIREMENTS NOT MET"; echo "Please address the issues above before proceeding."; fi

If you see "✅ YOUR SYSTEM IS READY", proceed to Step 2.

## Step 2: Install Container Platform

Run the system verification from the README first.

If you don't have Docker or Podman, we recommend **Podman** because:
- Rootless operation (better security)
- No background daemon (lighter resource usage)
- Drop-in Docker replacement (same commands)
- Better suited for research and validation workflows

### Install Podman (Recommended)

**Ubuntu/Debian:**

    sudo apt-get update
    sudo apt-get install -y podman

**Fedora:**

    sudo dnf install -y podman

**macOS (via Homebrew):**

    brew install podman
    podman machine init
    podman machine start

Verify: podman --version

### Install Docker (Alternative)

**Ubuntu/Debian:**

    curl -fsSL https://get.docker.com -o get-docker.sh
    sudo sh get-docker.sh
    sudo usermod -aG docker $USER
    newgrp docker

**macOS:**

Download Docker Desktop: https://docs.docker.com/desktop/mac/install/

Verify: docker --version

## Installation Steps

### 1. Clone Repository

    git clone https://github.com/rsleiberin/open-darf.git
    cd open-darf

### 2. Run Installation

    ./install

This will:
- Deploy infrastructure (Neo4j, PostgreSQL, Qdrant, Redis, MinIO)
- Initialize database schemas
- Verify service health
- Create necessary directories

### 3. Run Validation

    ./validate

This generates your validation receipt in var/receipts/open-darf/

### 4. Submit Evidence (Optional)

    export GITHUB_TOKEN="your_token"
    ./scripts/validate-and-submit.sh

### 5. Cleanup

    ./cleanup

## Troubleshooting

**Podman not found**: Restart terminal after installation or run newgrp
**Port conflicts**: Stop other containers with podman/docker ps and stop them
**Permission errors**: Add user to docker group or use rootless podman
**macOS Podman machine**: Ensure podman machine is started

## Next Steps

See VALIDATION-GUIDE.md for understanding your results.
