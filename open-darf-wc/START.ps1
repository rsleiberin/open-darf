# ===
# ===
# ===
Write-Host "=== Open-DARF · Start (Windows convenience) ==="
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\validator_acceptance.ps1
