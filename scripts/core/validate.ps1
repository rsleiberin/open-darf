# Open-DARF Comprehensive Validation (PowerShell)
param(
    [switch]$SkipConstitutional
)

$ErrorActionPreference = "Stop"

Write-Host ""
Write-Host "=== Open-DARF Validation ===" -ForegroundColor Cyan
Write-Host "Comprehensive: Document Ingestion + Constitutional Validation"
Write-Host ""

# [1/3] Check Docker daemon
Write-Host "[1/3] Checking Docker infrastructure..." -ForegroundColor Yellow
try {
    docker ps | Out-Null
    Write-Host "OK Docker daemon is running" -ForegroundColor Green
} catch {
    Write-Host "X ERROR: Docker daemon not running" -ForegroundColor Red
    exit 1
}

$Containers = docker ps --format "{{.Names}}" 2>$null
$ContainerCount = ($Containers | Measure-Object).Count
Write-Host "OK Found $ContainerCount running containers" -ForegroundColor Green

# [2/3] Create receipt directory
Write-Host ""
Write-Host "[2/3] Preparing receipt directory..." -ForegroundColor Yellow
New-Item -ItemType Directory -Force -Path var/receipts/open-darf | Out-Null
Write-Host "OK Receipt directory ready" -ForegroundColor Green

# [3/3] Run comprehensive validation
if (-not $SkipConstitutional) {
    Write-Host ""
    Write-Host "[3/3] Running comprehensive validation..." -ForegroundColor Yellow
    $Timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
    $ReceiptPath = "var/receipts/open-darf/validation_$Timestamp.json"
    
    try {
        $ErrorOutput = [System.IO.Path]::GetTempFileName()
        & .\scripts\internal\comprehensive_validation.ps1 2>$ErrorOutput | Out-File -FilePath $ReceiptPath -Encoding UTF8
        
        Write-Host "OK Comprehensive validation complete" -ForegroundColor Green
        
        $Receipt = Get-Content $ReceiptPath | ConvertFrom-Json
        Write-Host ""
        Write-Host "Results:" -ForegroundColor Cyan
        Write-Host "  Test: $($Receipt.test_scenario)" -ForegroundColor White
        Write-Host "  Document SHA256: $($Receipt.document_ingestion.sha256_hash.Substring(0,16))..." -ForegroundColor White
        Write-Host "  Validations: $($Receipt.constitutional_validations.Length) rules tested" -ForegroundColor White
        Write-Host "  Total time: $($Receipt.pipeline_performance.total_end_to_end_ms)ms" -ForegroundColor White
        Write-Host "  Database I/O: $($Receipt.pipeline_performance.percentage_breakdown.database_io)%" -ForegroundColor White
        
        Write-Host ""
        Write-Host "  Receipt: $ReceiptPath" -ForegroundColor White
    } catch {
        Write-Host "! Validation encountered an error" -ForegroundColor Yellow
        Get-Content $ErrorOutput
        exit 1
    } finally {
        if (Test-Path $ErrorOutput) { Remove-Item $ErrorOutput -Force }
    }
} else {
    Write-Host ""
    Write-Host "[3/3] Skipping validation (--SkipConstitutional)" -ForegroundColor Yellow
}

Write-Host ""
Write-Host "=== Validation Complete ===" -ForegroundColor Green
exit 0
