# ===
# ===
# ===
Write-Host "=== Open-DARF · CI Evidence Publisher (Windows) ==="
$root = Split-Path -Parent $MyInvocation.MyCommand.Path | Split-Path -Parent
$results = Join-Path $root 'results'
$pub = Join-Path $results 'publish'
New-Item -ItemType Directory -Force -Path $pub | Out-Null

$latest = Get-ChildItem $results -Filter 'evidence_*' | Sort-Object LastWriteTime -Descending | Select-Object -First 1
if (-not $latest) { Write-Host "[!] No evidence archives found in $results"; exit 2 }

Copy-Item $latest.FullName -Destination $pub -Force
$dest = Join-Path $pub $latest.Name

$sha = (Get-FileHash -Algorithm SHA256 $dest).Hash
$size = (Get-Item $dest).Length
$host = $env:COMPUTERNAME
$ts = (Get-Date).ToString('s')

@{
  ts = $ts
  host = $host
  file = $latest.Name
  size_bytes = $size
  sha256 = $sha
} | ConvertTo-Json | Out-File -Encoding utf8 (Join-Path $pub 'evidence_manifest.json')

Write-Host "[✓] Published: $dest"
Write-Host "[✓] Manifest : $(Join-Path $pub 'evidence_manifest.json')"
