#Requires -Version 5.1
<#
.SYNOPSIS
    Open-DARF Cleanup Script for Windows
.DESCRIPTION
    Removes all Docker infrastructure for Open-DARF.
    Stops and removes containers, networks, and optionally volumes.
.PARAMETER KeepVolumes
    If specified, preserves data volumes (databases, etc.)
.EXAMPLE
    .\cleanup.ps1
    .\cleanup.ps1 -KeepVolumes
.NOTES
    This will remove all Open-DARF containers and networks
#>

[CmdletBinding()]
param(
    [Parameter()]
    [switch]$KeepVolumes
)

$ErrorActionPreference = "Stop"

Write-Host "`n=== Open-DARF Cleanup ===" -ForegroundColor Cyan
Write-Host "Removing Docker infrastructure`n" -ForegroundColor White

# Check Docker is running
Write-Host "[1/3] Checking Docker daemon..." -ForegroundColor Yellow
try {
    docker ps | Out-Null
    Write-Host "[OK] Docker daemon is running" -ForegroundColor Green
} catch {
    Write-Host "[ERROR] ERROR: Docker daemon not running" -ForegroundColor Red
    Write-Host "Please start Docker Desktop and try again" -ForegroundColor Yellow
    exit 1
}

# Determine compose command
$composeCmd = $null
if (Get-Command docker-compose -ErrorAction SilentlyContinue) {
    $composeCmd = "docker-compose"
} elseif ((docker compose version 2>$null) -and ($LASTEXITCODE -eq 0)) {
    $composeCmd = "docker compose"
}

if (-not $composeCmd) {
    Write-Host "[WARNING]  WARNING: Docker Compose not found" -ForegroundColor Yellow
    Write-Host "Attempting manual cleanup..." -ForegroundColor Yellow
}

# Stop and remove containers
Write-Host "`n[2/3] Stopping and removing containers..." -ForegroundColor Yellow

if ($composeCmd) {
    try {
        if ($KeepVolumes) {
            Write-Host "[INFO]  Keeping data volumes (use without -KeepVolumes to remove)" -ForegroundColor Cyan
            if ($composeCmd -eq "docker-compose") {
                docker-compose down
            } else {
                docker compose down
            }
        } else {
            Write-Host "[WARNING]  Removing data volumes (all data will be lost)" -ForegroundColor Yellow
            if ($composeCmd -eq "docker-compose") {
                docker-compose down -v
            } else {
                docker compose down -v
            }
        }
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "[OK] Containers and networks removed" -ForegroundColor Green
        } else {
            throw "Docker Compose cleanup failed"
        }
    } catch {
        Write-Host "[WARNING]  Compose cleanup failed, trying manual cleanup" -ForegroundColor Yellow
    }
}

# Verify cleanup
Write-Host "`n[3/3] Verifying cleanup..." -ForegroundColor Yellow

try {
    $remainingContainers = docker ps -a --format "{{.Names}}" | Select-String -Pattern "darf" -CaseSensitive
    
    if ($remainingContainers) {
        Write-Host "[WARNING]  Some DARF containers still exist:" -ForegroundColor Yellow
        foreach ($container in $remainingContainers) {
            Write-Host "  - $container" -ForegroundColor White
        }
        Write-Host "`nManually remove with:" -ForegroundColor Yellow
        Write-Host "  docker rm -f CONTAINER_NAME" -ForegroundColor Cyan
    } else {
        Write-Host "[OK] No DARF containers remaining" -ForegroundColor Green
    }
} catch {
    Write-Host "[INFO]  Could not verify container cleanup" -ForegroundColor Cyan
}

try {
    $remainingNetworks = docker network ls --format "{{.Name}}" | Select-String -Pattern "darf" -CaseSensitive
    
    if ($remainingNetworks) {
        Write-Host "[WARNING]  Some DARF networks still exist:" -ForegroundColor Yellow
        foreach ($network in $remainingNetworks) {
            Write-Host "  - $network" -ForegroundColor White
        }
        Write-Host "`nManually remove with:" -ForegroundColor Yellow
        Write-Host "  docker network rm NETWORK_NAME" -ForegroundColor Cyan
    } else {
        Write-Host "[OK] No DARF networks remaining" -ForegroundColor Green
    }
} catch {
    Write-Host "[INFO]  Could not verify network cleanup" -ForegroundColor Cyan
}

if (-not $KeepVolumes) {
    try {
        $remainingVolumes = docker volume ls --format "{{.Name}}" | Select-String -Pattern "darf" -CaseSensitive
        
        if ($remainingVolumes) {
            Write-Host "[WARNING]  Some DARF volumes still exist:" -ForegroundColor Yellow
            foreach ($volume in $remainingVolumes) {
                Write-Host "  - $volume" -ForegroundColor White
            }
            Write-Host "`nManually remove with:" -ForegroundColor Yellow
            Write-Host "  docker volume rm VOLUME_NAME" -ForegroundColor Cyan
        } else {
            Write-Host "[OK] No DARF volumes remaining" -ForegroundColor Green
        }
    } catch {
        Write-Host "[INFO]  Could not verify volume cleanup" -ForegroundColor Cyan
    }
}

Write-Host "`n=== Cleanup Complete ===" -ForegroundColor Cyan
Write-Host "To reinstall, run: .\install.ps1" -ForegroundColor White
exit 0
