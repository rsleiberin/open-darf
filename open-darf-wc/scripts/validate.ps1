# ===
# ===
# ===
Write-Host "=== Open-DARF · Windows validation with heartbeat ==="

function Start-Heartbeat([string]$Msg) {
  if ($script:hbTimer) { Stop-Heartbeat }
  $script:hbTimer = New-Object System.Timers.Timer
  $script:hbTimer.Interval = 2000
  $script:hbTimer.AutoReset = $true
  $script:hbTimer.add_Elapsed({ Write-Host "[HB] $Msg — $(Get-Date -Format HH:mm:ss)" })
  $script:hbTimer.Start()
}
function Stop-Heartbeat {
  if ($script:hbTimer) { $script:hbTimer.Stop(); $script:hbTimer.Dispose(); $script:hbTimer = $null }
}

Set-Location -Path "$PSScriptRoot\.."
New-Item -ItemType Directory -Force -Path results | Out-Null

Start-Heartbeat "Collecting system info"
$sysinfo = @{
  hostname = $env:COMPUTERNAME
  os = (Get-CimInstance Win32_OperatingSystem).Caption
  cpu = (Get-CimInstance Win32_Processor).Name
  ram_gb = [math]::Round(((Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory/1GB),2)
  docker = (docker --version)
  ts = (Get-Date).ToString("s")
}
$sysinfo | ConvertTo-Json | Out-File -Encoding utf8 "results\sysinfo.json"
Stop-Heartbeat

Start-Heartbeat "Probing MinIO"
$hcMinio="fail"
foreach ($i in 1..30) { try { curl.exe -fsS http://localhost:9000/minio/health/live | Out-Null; $hcMinio="ok"; break } catch { Start-Sleep -Seconds 2 } }
Stop-Heartbeat

Start-Heartbeat "Probing Qdrant"
$hcQdrant="fail"
foreach ($i in 1..45) { try { curl.exe -fsS http://localhost:6333/healthz | Out-Null; $hcQdrant="ok"; break } catch { Start-Sleep -Seconds 2 } }
Stop-Heartbeat

@{minio=$hcMinio; qdrant=$hcQdrant} | ConvertTo-Json | Out-File -Encoding utf8 "results\health.json"

Start-Heartbeat "Generating evidence stub"
$random = [System.Guid]::NewGuid().ToString("N")
$hash = (echo $random | openssl sha256).Split(" ").GetValue(1)
@{ nonce=$random; sha256=$hash; ts=(Get-Date).ToString("s") } | ConvertTo-Json | Out-File -Encoding utf8 "results\evidence_stub.json"
Stop-Heartbeat

Write-Host "[✓] Validation receipts written to 'results/'."
