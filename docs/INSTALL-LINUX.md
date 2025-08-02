# Linux/macOS Installation Guide

## Step 1: System Verification

Run this bash command to verify your system meets requirements:

    echo "=== OPEN-DARF SYSTEM CHECK ==="; ready=true; os_name=$(uname -s); os_version=$(uname -r); ram_gb=$(free -g 2>/dev/null | awk '/^Mem:/{print $2}' || sysctl -n hw.memsize 2>/dev/null | awk '{print int($1/1024/1024/1024)}'); disk_gb=$(df -BG / 2>/dev/null | awk 'NR==2{print $4}' | sed 's/G//' || df -g / 2>/dev/null | awk 'NR==2{print $4}'); docker_ver=$(command -v docker >/dev/null 2>&1 && docker --version || echo ""); podman_ver=$(command -v podman >/dev/null 2>&1 && podman --version || echo ""); if [ -n "$os_name" ]; then echo "✅ OS: $os_name $os_version"; else echo "❌ OS: Unknown"; ready=false; fi; if [ "$ram_gb" -ge 8 ]; then echo "✅ RAM: ${ram_gb}GB"; else echo "❌ RAM: ${ram_gb}GB - Need 8GB+"; ready=false; fi; if [ "${disk_gb}" -ge 15 ]; then echo "✅ Disk: ${disk_gb}GB free"; else echo "❌ Disk: ${disk_gb}GB free - Need 15GB+"; ready=false; fi; if [ -z "$docker_ver" ] && [ -z "$podman_ver" ]; then echo "❌ Container Platform: Not found"; echo "  Install Docker: https://docs.docker.com/engine/install/"; echo "  Install Podman: https://podman.io/getting-started/installation"; ready=false; else [ -n "$docker_ver" ] && echo "✅ Docker: $docker_ver"; [ -n "$podman_ver" ] && echo "✅ Podman: $podman_ver"; fi; echo ""; echo "=== RESULT ==="; if [ "$ready" = true ]; then echo "✅ YOUR SYSTEM IS READY FOR OPEN-DARF!"; echo "Next step: Proceed to installation"; else echo "❌ SYSTEM REQUIREMENTS NOT MET"; echo "Please address the issues above before proceeding."; fi

If you see "✅ YOUR SYSTEM IS READY", proceed to Step 2.

## Step 2: Install Container Platform

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

Verify: `podman --version`

### Install Docker (Alternative)

**Ubuntu/Debian:**

    curl -fsSL https://get.docker.com -o get-docker.sh
    sudo sh get-docker.sh
    sudo usermod -aG docker $USER
    newgrp docker

**macOS:**

Download Docker Desktop: https://docs.docker.com/desktop/mac/install/

Verify: `docker --version`

## Step 3: Clone or Update Repository

    # Handle existing directory
    if [ -d "open-darf" ]; then
        echo "Repository directory exists. Updating..."
        cd open-darf
        if [ -d ".git" ]; then
            git fetch origin
            git reset --hard origin/main
            git pull origin main
            echo "Repository updated successfully"
        else
            echo "ERROR: 'open-darf' exists but is not a git repository"
            echo "Please manually delete or rename the directory"
            exit 1
        fi
    else
        echo "Cloning repository..."
        git clone https://github.com/rsleiberin/open-darf.git
        cd open-darf
        echo "Repository cloned successfully"
    fi

## Step 4: Run Installation

    ./install

This will:
- Deploy infrastructure (Neo4j, PostgreSQL, Qdrant, Redis, MinIO)
- Initialize database schemas
- Verify service health
- Create necessary directories

Expected runtime: 2-5 minutes

## Step 5: Run Validation

    ./validate

This generates your validation receipt in `var/receipts/open-darf/`

Expected runtime: 3-7 minutes

## Step 6: Submit Evidence (Optional)

To contribute your validation evidence to the research:

    export GITHUB_TOKEN="your_token"
    ./scripts/validate-and-submit.sh

Get a token at: https://github.com/settings/tokens (requires 'repo' scope)

## Step 7: Cleanup

    ./cleanup

Removes all containers, networks, and generated data.

## Troubleshooting

**Permission denied**: Make scripts executable with `chmod +x install validate cleanup`

**Podman not found**: Restart terminal after installation or run `newgrp`

**Port conflicts**: Stop other containers with `docker/podman ps` then `docker/podman stop [id]`

**Docker daemon not running**: Start with `sudo systemctl start docker`

**macOS Podman machine**: Ensure started with `podman machine start`

**Permission errors (Docker)**: Add user to docker group: `sudo usermod -aG docker $USER` then logout/login

## Next Steps

Your validation receipt contains evidence of:
- Infrastructure deployment success
- Constitutional constraint performance
- Formal verification correspondence
- Cross-platform feasibility

This contributes to demonstrating that mathematical AI governance works on consumer hardware.
