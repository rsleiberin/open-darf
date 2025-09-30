# Windows Installation Guide

## Prerequisites Check

## Step 1: System Verification

Run this PowerShell command to verify your system meets requirements:

    $r = @{}; $r.os = [System.Environment]::OSVersion.Version; $r.ram = [Math]::Round((Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory / 1GB, 2); $r.disk = [Math]::Round((Get-CimInstance Win32_LogicalDisk -Filter "DriveType=3" | Measure-Object -Property FreeSpace -Sum).Sum / 1GB, 2); $r.docker = if (Get-Command docker -ErrorAction SilentlyContinue) { (docker --version) } else { $null }; $r.podman = if (Get-Command podman -ErrorAction SilentlyContinue) { (podman --version) } else { $null }; Write-Host "`n=== OPEN-DARF SYSTEM CHECK ===" -ForegroundColor Cyan; $ready = $true; if ($r.os.Major -lt 10) { Write-Host "❌ Windows: $($r.os.Major).$($r.os.Minor) - Need Windows 10+" -ForegroundColor Red; $ready = $false } else { Write-Host "✅ Windows: $($r.os.Major).$($r.os.Minor)" -ForegroundColor Green }; if ($r.ram -lt 8) { Write-Host "❌ RAM: $($r.ram)GB - Need 8GB+" -ForegroundColor Red; $ready = $false } else { Write-Host "✅ RAM: $($r.ram)GB" -ForegroundColor Green }; if ($r.disk -lt 15) { Write-Host "❌ Disk: $($r.disk)GB free - Need 15GB+" -ForegroundColor Red; $ready = $false } else { Write-Host "✅ Disk: $($r.disk)GB free" -ForegroundColor Green }; if (!$r.docker -and !$r.podman) { Write-Host "❌ Container Platform: Not found - Install Docker or Podman" -ForegroundColor Red; Write-Host "  Docker: https://docs.docker.com/desktop/windows/" -ForegroundColor Yellow; Write-Host "  Podman: https://podman.io/getting-started/installation" -ForegroundColor Yellow; $ready = $false } else { if ($r.docker) { Write-Host "✅ Docker: $($r.docker)" -ForegroundColor Green }; if ($r.podman) { Write-Host "✅ Podman: $($r.podman)" -ForegroundColor Green } }; Write-Host "`n=== RESULT ===" -ForegroundColor Cyan; if ($ready) { Write-Host "✅ YOUR SYSTEM IS READY FOR OPEN-DARF!" -ForegroundColor Green -BackgroundColor Black; Write-Host "Next step: Proceed to installation" -ForegroundColor Yellow } else { Write-Host "❌ SYSTEM REQUIREMENTS NOT MET" -ForegroundColor Red -BackgroundColor Black; Write-Host "Please address the issues above before proceeding." -ForegroundColor Yellow }

If you see "✅ YOUR SYSTEM IS READY", proceed to Step 2.

## Step 2: Install Container Platform

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
