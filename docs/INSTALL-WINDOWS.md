# Windows Installation Guide

## Prerequisites Check

Run the system verification from the README first.

If you don't have Docker or Podman, we recommend **Podman Desktop** because:
- Rootless operation (better security)
- No background daemon (lighter resource usage)
- Drop-in Docker replacement (same commands)
- Better suited for research and validation workflows

### Install Podman Desktop (Recommended)

1. Download: https://podman-desktop.io/downloads/windows
2. Run installer and follow prompts
3. Restart terminal
4. Verify: podman --version

### Install Docker Desktop (Alternative)

1. Download: https://docs.docker.com/desktop/windows/install/
2. Run installer and enable WSL 2 backend
3. Restart terminal  
4. Verify: docker --version

## Installation Steps

### 1. Clone Repository

    git clone https://github.com/rsleiberin/open-darf.git
    cd open-darf

### 2. Run Installation

    .\install.ps1

This will:
- Deploy infrastructure (Neo4j, PostgreSQL, Qdrant, Redis, MinIO)
- Initialize database schemas
- Verify service health
- Create necessary directories

### 3. Run Validation

    .\validate.ps1

This generates your validation receipt in var/receipts/open-darf/

### 4. Submit Evidence (Optional)

    .\scripts\Validate-OpenDARF.ps1 -GitHubToken "your_token"

### 5. Cleanup

    .\cleanup.ps1

## Troubleshooting

**Podman not found**: Restart terminal after installation
**Port conflicts**: Stop other containers or use docker/podman ps to check
**Permission errors**: Run PowerShell as Administrator
**WSL issues**: Ensure WSL 2 is installed and updated

## Next Steps

See VALIDATION-GUIDE.md for understanding your results.
