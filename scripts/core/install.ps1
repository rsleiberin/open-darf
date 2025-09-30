#Requires -Version 5.1
<#
.SYNOPSIS
    Open-DARF Installation Script for Windows
.DESCRIPTION
    Deploys Docker infrastructure for constitutional AI validation on Windows systems.
#>

[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"

Write-Host ""
Write-Host "=== Open-DARF Installation ===" -ForegroundColor Cyan
Write-Host "Deploying Docker infrastructure for constitutional AI validation" -ForegroundColor White
Write-Host ""

# Check Docker
Write-Host "[1/5] Checking Docker..." -ForegroundColor Yellow
if (-not (Get-Command docker -ErrorAction SilentlyContinue)) {
    Write-Host "ERROR: Docker not found" -ForegroundColor Red
    Write-Host "Install: https://docs.docker.com/desktop/windows/" -ForegroundColor Yellow
    exit 1
}

Write-Host "Docker found: $(docker --version)" -ForegroundColor Green

# Check Docker daemon
Write-Host ""
Write-Host "[2/5] Checking Docker daemon..." -ForegroundColor Yellow
try {
    docker ps | Out-Null
    Write-Host "Docker daemon is running" -ForegroundColor Green
} catch {
    Write-Host "ERROR: Docker daemon not running" -ForegroundColor Red
    Write-Host "Start Docker Desktop and try again" -ForegroundColor Yellow
    exit 1
}

# Check Docker Compose - prioritize newer plugin version
Write-Host ""
Write-Host "[3/5] Checking Docker Compose..." -ForegroundColor Yellow
$composeCmd = $null

# Try docker compose (newer plugin - preferred)
if ((docker compose version 2>$null) -and ($LASTEXITCODE -eq 0)) {
    $composeCmd = "docker compose"
    Write-Host "Using Docker Compose plugin (recommended)" -ForegroundColor Green
}
# Fallback to docker-compose (older standalone)
elseif (Get-Command docker-compose -ErrorAction SilentlyContinue) {
    $composeCmd = "docker-compose"
    Write-Host "Using legacy docker-compose (consider updating)" -ForegroundColor Yellow
}

if (-not $composeCmd) {
    Write-Host "ERROR: Docker Compose not available" -ForegroundColor Red
    exit 1
}

# Check system resources
Write-Host ""
Write-Host "[4/5] Checking system resources..." -ForegroundColor Yellow
$totalRAM = [Math]::Round((Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory / 1GB, 2)
$freeDisk = [Math]::Round((Get-CimInstance Win32_LogicalDisk -Filter "DriveType=3" | Measure-Object -Property FreeSpace -Sum).Sum / 1GB, 2)

if ($totalRAM -lt 8) {
    Write-Host "WARNING: Only ${totalRAM}GB RAM. 8GB+ recommended" -ForegroundColor Yellow
} else {
    Write-Host "RAM: ${totalRAM}GB" -ForegroundColor Green
}

if ($freeDisk -lt 15) {
    Write-Host "WARNING: Only ${freeDisk}GB free. 15GB+ recommended" -ForegroundColor Yellow
} else {
    Write-Host "Disk: ${freeDisk}GB free" -ForegroundColor Green
}

# Check .env
if (-not (Test-Path ".env")) {
    if (Test-Path ".env.sample") {
        Write-Host ""
        Write-Host "Creating .env from .env.sample" -ForegroundColor Cyan
        Copy-Item ".env.sample" ".env"
    }
}

# Deploy
Write-Host ""
Write-Host "[5/5] Deploying infrastructure..." -ForegroundColor Yellow
Write-Host "This may take several minutes on first run..." -ForegroundColor White

try {
    # Use whichever compose command we determined works
    & $composeCmd.Split() up -d
    
    if ($LASTEXITCODE -ne 0) {
        throw "Docker Compose failed with exit code $LASTEXITCODE"
    }

    Write-Host ""
    Write-Host "Infrastructure deployed successfully!" -ForegroundColor Green
    Write-Host ""
    Write-Host "Check status: docker ps" -ForegroundColor Cyan
    Write-Host "Run validation: .\validate.ps1" -ForegroundColor Cyan
    Write-Host "Cleanup: .\cleanup.ps1" -ForegroundColor Cyan

} catch {
    Write-Host ""
    Write-Host "ERROR: Deployment failed" -ForegroundColor Red
    Write-Host $_.Exception.Message -ForegroundColor Red
    Write-Host ""
    Write-Host "Check logs: $composeCmd logs" -ForegroundColor Yellow
    exit 1
}

Write-Host ""
Write-Host "=== Installation Complete ===" -ForegroundColor Cyan
exit 0
