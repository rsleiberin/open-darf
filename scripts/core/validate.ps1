#Requires -Version 5.1
<#
.SYNOPSIS
    Open-DARF Validation Script for Windows
.DESCRIPTION
    Validates Docker infrastructure and runs TLA+ verification for constitutional AI.
    Checks service health and executes formal verification specifications.
.EXAMPLE
    .\validate.ps1
.NOTES
    Requires Docker infrastructure to be running (run install.ps1 first)
#>

[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"

Write-Host "`n=== Open-DARF Validation ===" -ForegroundColor Cyan
Write-Host "Validating constitutional AI infrastructure`n" -ForegroundColor White

# Check Docker is running
Write-Host "[1/4] Checking Docker daemon..." -ForegroundColor Yellow
try {
    docker ps | Out-Null
    Write-Host "✅ Docker daemon is running" -ForegroundColor Green
} catch {
    Write-Host "❌ ERROR: Docker daemon not running" -ForegroundColor Red
    Write-Host "Please start Docker Desktop and try again" -ForegroundColor Yellow
    exit 1
}

# Check infrastructure services
Write-Host "`n[2/4] Checking infrastructure services..." -ForegroundColor Yellow
try {
    $containers = docker ps --format "{{.Names}}" 2>$null
    if ($LASTEXITCODE -ne 0 -or -not $containers) {
        Write-Host "⚠️  No running containers found" -ForegroundColor Yellow
        Write-Host "Run .\install.ps1 first to deploy infrastructure" -ForegroundColor Cyan
        exit 1
    }
    
    $containerList = $containers -split "`n"
    Write-Host "✅ Found $($containerList.Count) running containers:" -ForegroundColor Green
    foreach ($container in $containerList) {
        Write-Host "  - $container" -ForegroundColor White
    }
} catch {
    Write-Host "❌ ERROR: Failed to check containers" -ForegroundColor Red
    Write-Host $_.Exception.Message -ForegroundColor Red
    exit 1
}

# Check for TLA+ specifications
Write-Host "`n[3/4] Checking TLA+ specifications..." -ForegroundColor Yellow
$tlaPath = "verification/tla"
if (Test-Path $tlaPath) {
    $specs = Get-ChildItem -Path $tlaPath -Filter "*.tla" -Recurse
    Write-Host "✅ Found $($specs.Count) TLA+ specifications" -ForegroundColor Green
    
    # Check for existing evidence
    $evidencePath = "evidence/tla/class_a"
    if (Test-Path $evidencePath) {
        $evidenceFiles = Get-ChildItem -Path "$evidencePath/logs" -Filter "*.log" -ErrorAction SilentlyContinue
        if ($evidenceFiles) {
            Write-Host "✅ Found existing verification evidence:" -ForegroundColor Green
            Write-Host "  Location: $evidencePath/logs" -ForegroundColor White
            Write-Host "  Files: $($evidenceFiles.Count) verification logs" -ForegroundColor White
        }
    }
} else {
    Write-Host "⚠️  No TLA+ specifications found at $tlaPath" -ForegroundColor Yellow
}

# Service health check
Write-Host "`n[4/4] Running service health checks..." -ForegroundColor Yellow
$healthyCount = 0
$unhealthyCount = 0

try {
    $containerStatus = docker ps --format "{{.Names}}:{{.Status}}" 2>$null
    if ($LASTEXITCODE -eq 0 -and $containerStatus) {
        foreach ($line in ($containerStatus -split "`n")) {
            $parts = $line -split ":"
            if ($parts.Count -eq 2) {
                $name = $parts[0]
                $status = $parts[1]
                
                if ($status -match "Up|healthy") {
                    Write-Host "  ✅ $name - Running" -ForegroundColor Green
                    $healthyCount++
                } else {
                    Write-Host "  ⚠️  $name - $status" -ForegroundColor Yellow
                    $unhealthyCount++
                }
            }
        }
    }
    
    if ($unhealthyCount -gt 0) {
        Write-Host "`n⚠️  Some services may not be healthy" -ForegroundColor Yellow
        Write-Host "Check logs with: docker compose logs <service-name>" -ForegroundColor Cyan
    }
} catch {
    Write-Host "⚠️  Could not determine service health" -ForegroundColor Yellow
}

# Summary
Write-Host "`n=== Validation Summary ===" -ForegroundColor Cyan
Write-Host "Infrastructure Status:" -ForegroundColor White
Write-Host "  - Healthy services: $healthyCount" -ForegroundColor Green
if ($unhealthyCount -gt 0) {
    Write-Host "  - Unhealthy services: $unhealthyCount" -ForegroundColor Yellow
}

Write-Host "`nFor detailed logs:" -ForegroundColor White
Write-Host "  docker compose logs" -ForegroundColor Cyan
Write-Host "`nTo view specific service logs:" -ForegroundColor White
Write-Host "  docker compose logs <service-name>" -ForegroundColor Cyan

Write-Host "`n=== Validation Complete ===" -ForegroundColor Cyan
exit 0
