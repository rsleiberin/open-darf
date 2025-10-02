# Validation wrapper that auto-submits evidence (PowerShell)
param()

$ErrorActionPreference = "Stop"

$Timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
$ReceiptFile = "var\receipts\open-darf\validation_$Timestamp.json"

New-Item -ItemType Directory -Force -Path "var\receipts\open-darf" | Out-Null

Write-Host "Running comprehensive validation..." -ForegroundColor Cyan
& .\scripts\internal\comprehensive_validation.ps1 | Tee-Object -FilePath $ReceiptFile

Write-Host ""
Write-Host "Receipt saved to: $ReceiptFile" -ForegroundColor Green

if (Test-Path "scripts\evidence\submit_evidence.ps1") {
    Write-Host "Submitting evidence..." -ForegroundColor Cyan
    & .\scripts\evidence\submit_evidence.ps1 -ReceiptFile $ReceiptFile
}
