# Windows Installation Guide

## Step 1: System Verification

Run this PowerShell command to verify your system meets requirements:

    $r = @{}; $r.os = [System.Environment]::OSVersion.Version; $r.ram = [Math]::Round((Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory / 1GB, 2); $r.disk = [Math]::Round((Get-CimInstance Win32_LogicalDisk -Filter "DriveType=3" | Measure-Object -Property FreeSpace -Sum).Sum / 1GB, 2); $r.docker = if (Get-Command docker -ErrorAction SilentlyContinue) { (docker --version) } else { $null }; $r.podman = if (Get-Command podman -ErrorAction SilentlyContinue) { (podman --version) } else { $null }; Write-Host "`n=== OPEN-DARF SYSTEM CHECK ===" -ForegroundColor Cyan; $ready = $true; if ($r.os.Major -lt 10) { Write-Host "❌ Windows: $($r.os.Major).$($r.os.Minor) - Need Windows 10+" -ForegroundColor Red; $ready = $false } else { Write-Host "✅ Windows: $($r.os.Major).$($r.os.Minor)" -ForegroundColor Green }; if ($r.ram -lt 8) { Write-Host "❌ RAM: $($r.ram)GB - Need 8GB+" -ForegroundColor Red; $ready = $false } else { Write-Host "✅ RAM: $($r.ram)GB" -ForegroundColor Green }; if ($r.disk -lt 15) { Write-Host "❌ Disk: $($r.disk)GB free - Need 15GB+" -ForegroundColor Red; $ready = $false } else { Write-Host "✅ Disk: $($r.disk)GB free" -ForegroundColor Green }; if (!$r.docker -and !$r.podman) { Write-Host "❌ Container Platform: Not found - Install Docker or Podman" -ForegroundColor Red; Write-Host "  Docker: https://docs.docker.com/desktop/windows/" -ForegroundColor Yellow; Write-Host "  Podman: https://podman.io/getting-started/installation" -ForegroundColor Yellow; $ready = $false } else { if ($r.docker) { Write-Host "✅ Docker: $($r.docker)" -ForegroundColor Green }; if ($r.podman) { Write-Host "✅ Podman: $($r.podman)" -ForegroundColor Green } }; Write-Host "`n=== RESULT ===" -ForegroundColor Cyan; if ($ready) { Write-Host "✅ YOUR SYSTEM IS READY FOR OPEN-DARF!" -ForegroundColor Green -BackgroundColor Black; Write-Host "Next step: Proceed to installation" -ForegroundColor Yellow } else { Write-Host "❌ SYSTEM REQUIREMENTS NOT MET" -ForegroundColor Red -BackgroundColor Black; Write-Host "Please address the issues above before proceeding." -ForegroundColor Yellow }

If you see "✅ YOUR SYSTEM IS READY", proceed to Step 2.

## Step 2: Install Container Platform

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

## Step 3: Clone or Update Repository

    # Handle existing directory
    if (Test-Path "open-darf") {
        Write-Host "Repository directory exists. Updating..." -ForegroundColor Yellow
        cd open-darf
        if (Test-Path ".git") {
            git fetch origin
            git reset --hard origin/main
            git pull origin main
            Write-Host "Repository updated successfully" -ForegroundColor Green
        } else {
            Write-Host "ERROR: 'open-darf' exists but is not a git repository" -ForegroundColor Red
            Write-Host "Please manually delete or rename the directory" -ForegroundColor Yellow
            exit
        }
    } else {
        Write-Host "Cloning repository..." -ForegroundColor Cyan
        git clone https://github.com/rsleiberin/open-darf.git
        cd open-darf
        Write-Host "Repository cloned successfully" -ForegroundColor Green
    }

## Step 4: Enable Script Execution

Windows security prevents running scripts by default. Enable for this session:

    Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass

This only affects your current PowerShell window and resets when you close it.

## Step 5: Run Installation

    .\install.ps1

This will:
- Deploy infrastructure (Neo4j, PostgreSQL, Qdrant, Redis, MinIO)
- Initialize database schemas
- Verify service health
- Create necessary directories

Expected runtime: 2-5 minutes

## Step 6: Run Validation

    .\validate.ps1

This generates your validation receipt in var/receipts/open-darf/

Expected runtime: 3-7 minutes

## Step 7: Submit Evidence (Optional)

To contribute your validation evidence to the research:

    .\scripts\Validate-OpenDARF.ps1 -GitHubToken "your_token"

Get a token at: https://github.com/settings/tokens (requires 'repo' scope)

## Step 8: Cleanup

    .\cleanup.ps1

Removes all containers, networks, and generated data.

## Troubleshooting

**Script execution error**: Run Set-ExecutionPolicy command from Step 4

**Podman not found**: Restart PowerShell after installation

**Port conflicts**: Stop other containers with docker/podman ps, then docker/podman stop [id]

**Permission errors**: Run PowerShell as Administrator (right-click, "Run as administrator")

**Docker not starting**: Ensure Docker Desktop is running (check system tray)

**WSL issues**: Update WSL with: wsl --update

## Next Steps

Your validation receipt contains evidence of:
- Infrastructure deployment success
- Constitutional constraint performance
- Formal verification correspondence
- Cross-platform feasibility

This contributes to demonstrating that mathematical AI governance works on consumer hardware.
