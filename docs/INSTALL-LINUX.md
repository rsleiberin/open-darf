# Linux/macOS Installation Guide

## Prerequisites Check

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
