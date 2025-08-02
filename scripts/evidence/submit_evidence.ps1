# Anonymous evidence submission after validation (PowerShell)
param([string]$ReceiptFile)

if (-not $ReceiptFile -or -not (Test-Path $ReceiptFile)) {
    Write-Host "Usage: .\submit_evidence.ps1 <receipt_file>" -ForegroundColor Red
    exit 1
}

$Timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
$Platform = "windows"
$ValidatorId = -join ((1..12) | ForEach-Object { '{0:x}' -f (Get-Random -Maximum 16) })

$EvidenceDir = "evidence\validation_receipts"
New-Item -ItemType Directory -Force -Path $EvidenceDir | Out-Null

$EvidenceFile = "$EvidenceDir\validation_${ValidatorId}_${Platform}_${Timestamp}.json"
Copy-Item $ReceiptFile $EvidenceFile

Write-Host "Evidence submitted anonymously" -ForegroundColor Green
Write-Host "Validator ID: $ValidatorId (random, not stored)"
Write-Host "Platform: $Platform"
Write-Host "File: $EvidenceFile"
