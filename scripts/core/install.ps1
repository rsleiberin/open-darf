#Requires -Version 5.1
<#
.SYNOPSIS
    Open-DARF Installation Script for Windows
.DESCRIPTION
    Deploys Docker infrastructure for constitutional AI validation on Windows systems.
    Checks prerequisites, validates system requirements, and deploys services.
.EXAMPLE
    .\install.ps1
.NOTES
    Requires Docker Desktop for Windows
#>

[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"

Write-Host "`n=== Open-DARF Installation ===" -ForegroundColor Cyan
Write-Host "Deploying Docker infrastructure for constitutional AI validation`n" -ForegroundColor White

# Check Docker availability
Write-Host "[1/5] Checking Docker..." -ForegroundColor Yellow
if (-not (Get-Command docker -ErrorAction SilentlyContinue)) {
    Write-Host "❌ ERROR: Docker not found" -ForegroundColor Red
    Write-Host "Please install Docker Desktop: https://docs.docker.com/desktop/windows/" -ForegroundColor Yellow
    exit 1
}

$dockerVersion = docker --version
Write-Host "✅ Docker found: $dockerVersion" -ForegroundColor Green

# Check Docker is running
Write-Host "`n[2/5] Checking Docker daemon..." -ForegroundColor Yellow
try {
    docker ps | Out-Null
    Write-Host "✅ Docker daemon is running" -ForegroundColor Green
} catch {
    Write-Host "❌ ERROR: Docker daemon not running" -ForegroundColor Red
    Write-Host "Please start Docker Desktop and try again" -ForegroundColor Yellow
    exit 1
}

# Check Docker Compose availability
Write-Host "`n[3/5] Checking Docker Compose..." -ForegroundColor Yellow
$composeCmd = $null
if (Get-Command docker-compose -ErrorAction SilentlyContinue) {
    $composeCmd = "docker-compose"
} elseif ((docker compose version 2>$null) -and ($LASTEXITCODE -eq 0)) {
    $composeCmd = "docker compose"
}

if (-not $composeCmd) {
    Write-Host "❌ ERROR: Docker Compose not available" -ForegroundColor Red
    Write-Host "Please install Docker Compose or update Docker Desktop" -ForegroundColor Yellow
    exit 1
}

Write-Host "✅ Docker Compose available: $composeCmd" -ForegroundColor Green

# Check system resources
Write-Host "`n[4/5] Checking system resources..." -ForegroundColor Yellow
$totalRAM = [Math]::Round((Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory / 1GB, 2)
$freeDisk = [Math]::Round((Get-CimInstance Win32_LogicalDisk -Filter "DriveType=3" | Measure-Object -Property FreeSpace -Sum).Sum / 1GB, 2)

if ($totalRAM -lt 8) {
    Write-Host "⚠️  WARNING: Only ${totalRAM}GB RAM detected. 8GB+ recommended" -ForegroundColor Yellow
} else {
    Write-Host "✅ RAM: ${totalRAM}GB" -ForegroundColor Green
}

if ($freeDisk -lt 15) {
    Write-Host "⚠️  WARNING: Only ${freeDisk}GB disk space free. 15GB+ recommended" -ForegroundColor Yellow
} else {
    Write-Host "✅ Disk: ${freeDisk}GB free" -ForegroundColor Green
}

# Check .env file
if (-not (Test-Path ".env")) {
    if (Test-Path ".env.sample") {
        Write-Host "`nℹ️  Creating .env from .env.sample" -ForegroundColor Cyan
        Copy-Item ".env.sample" ".env"
    } else {
        Write-Host "⚠️  WARNING: No .env or .env.sample found" -ForegroundColor Yellow
    }
}

# Deploy infrastructure
Write-Host "`n[5/5] Deploying infrastructure..." -ForegroundColor Yellow
Write-Host "This may take several minutes on first run (downloading images)..." -ForegroundColor White

try {
    if ($composeCmd -eq "docker-compose") {
        docker-compose up -d
    } else {
        docker compose up -d
    }
    
    if ($LASTEXITCODE -ne 0) {
        throw "Docker Compose failed"
    }
    
    Write-Host "`n✅ Infrastructure deployed successfully!" -ForegroundColor Green
    Write-Host "`nServices are starting up. You can check status with:" -ForegroundColor White
    Write-Host "  docker ps" -ForegroundColor Cyan
    Write-Host "`nTo validate the system, run:" -ForegroundColor White
    Write-Host "  .\validate.ps1" -ForegroundColor Cyan
    Write-Host "`nTo remove all infrastructure:" -ForegroundColor White
    Write-Host "  .\cleanup.ps1" -ForegroundColor Cyan
    
} catch {
    Write-Host "`n❌ ERROR: Deployment failed" -ForegroundColor Red
    Write-Host $_.Exception.Message -ForegroundColor Red
    Write-Host "`nCheck logs with: docker compose logs" -ForegroundColor Yellow
    exit 1
}

Write-Host "`n=== Installation Complete ===" -ForegroundColor Cyan
exit 0
