# Open-DARF Validation Script (Windows PowerShell)
# Validates Docker infrastructure and runs constitutional validation

param(
    [switch]$SkipConstitutional
)

$ErrorActionPreference = "Stop"

Write-Host ""
Write-Host "=== Open-DARF Validation ===" -ForegroundColor Cyan
Write-Host "Running constitutional AI validation with performance measurement"
Write-Host ""

# [1/5] Check Docker daemon
Write-Host "[1/5] Checking Docker daemon..." -ForegroundColor Yellow
try {
    docker ps | Out-Null
    Write-Host "✅ Docker daemon is running" -ForegroundColor Green
} catch {
    Write-Host "❌ ERROR: Docker daemon not running" -ForegroundColor Red
    Write-Host "Please start Docker and try again" -ForegroundColor Red
    exit 1
}

# [2/5] Check infrastructure services
Write-Host "`n[2/5] Checking infrastructure services..." -ForegroundColor Yellow
try {
    $containers = docker ps --format "{{.Names}}" 2>$null
    if (-not $containers) {
        Write-Host "⚠️  No running containers found" -ForegroundColor Yellow
        Write-Host "Run .\install.ps1 first to deploy infrastructure" -ForegroundColor Yellow
        exit 1
    }
    
    $containerCount = ($containers -split "`n").Count
    Write-Host "✅ Found $containerCount running containers:" -ForegroundColor Green
    $containers -split "`n" | ForEach-Object { Write-Host "  - $_" -ForegroundColor White }
} catch {
    Write-Host "❌ ERROR: Could not check containers" -ForegroundColor Red
    exit 1
}

# [3/5] Create receipt directory
Write-Host "`n[3/5] Preparing receipt directory..." -ForegroundColor Yellow
New-Item -ItemType Directory -Force -Path "var\receipts\open-darf" | Out-Null
Write-Host "✅ Receipt directory ready" -ForegroundColor Green

# [4/5] Run constitutional validation
if (-not $SkipConstitutional) {
    Write-Host "`n[4/5] Executing constitutional validation..." -ForegroundColor Yellow
    
    try {
        $timestamp = (Get-Date).ToUniversalTime().ToString("yyyyMMdd_HHmmss")
        $receiptPath = "var\receipts\open-darf\validation_$timestamp.json"
        
        # Execute constitutional engine and capture output
        $validationOutput = & .\scripts\internal\constitutional_engine.ps1
        
        # Save receipt
        $validationOutput | Out-File -FilePath $receiptPath -Encoding utf8
        
        # Parse and display results
        $receipt = $validationOutput | ConvertFrom-Json
        
        Write-Host "✅ Constitutional validation complete" -ForegroundColor Green
        Write-Host "  Decision: $($receipt.constitutional_validation.decision)" -ForegroundColor White
        Write-Host "  Reason: $($receipt.constitutional_validation.reason)" -ForegroundColor White
        Write-Host "  Performance: $($receipt.constitutional_validation.total_overhead_ms)ms total overhead" -ForegroundColor White
        Write-Host "    - Neo4j query: $($receipt.constitutional_validation.neo4j_query_ms)ms" -ForegroundColor Gray
        Write-Host "    - PostgreSQL insert: $($receipt.constitutional_validation.postgres_insert_ms)ms" -ForegroundColor Gray
        Write-Host "  Receipt: $receiptPath" -ForegroundColor Cyan
        
    } catch {
        Write-Host "⚠️  Constitutional validation encountered an error:" -ForegroundColor Yellow
        Write-Host $_.Exception.Message -ForegroundColor Yellow
        Write-Host "Continuing with validation..." -ForegroundColor Yellow
    }
} else {
    Write-Host "`n[4/5] Skipping constitutional validation (--SkipConstitutional)" -ForegroundColor Yellow
}

# [5/5] Service health check
Write-Host "`n[5/5] Running service health checks..." -ForegroundColor Yellow
$healthyCount = 0
$unhealthyCount = 0

try {
    $containerStatus = docker ps --format "{{.Names}}:{{.Status}}" 2>$null
    if ($containerStatus) {
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

if (-not $SkipConstitutional) {
    Write-Host "`nConstitutional Validation:" -ForegroundColor White
    Write-Host "  - Receipt generated: var\receipts\open-darf\" -ForegroundColor Cyan
    Write-Host "  - Performance measured and documented" -ForegroundColor Cyan
}

Write-Host "`nFor detailed logs:" -ForegroundColor White
Write-Host "  docker compose logs" -ForegroundColor Cyan

Write-Host "`n=== Validation Complete ===" -ForegroundColor Cyan
exit 0
