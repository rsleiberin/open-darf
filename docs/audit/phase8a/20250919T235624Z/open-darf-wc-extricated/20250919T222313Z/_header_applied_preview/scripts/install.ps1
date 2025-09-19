# DO NOT COMMIT THIS FILE — PREVIEW OF PROPOSED HEADER
# Header: Purpose
# One or two plain sentences describing what this file does and who runs it.

# Header: Inputs
# - Environment variables / CLI flags
# - External services called (if any)

# Header: Outputs
# - Files/receipts generated
# - Network side effects (ports/endpoints touched)

# Header: Data Flow
# Source → Transform/Validation → Sink (mention receipts directory)

# Header: Failure Modes & Recovery
# Common errors, detection cues, and operator actions.

# Header: Idempotence & Teardown
# What is safe to re-run; cleanup behavior.

# Header: Security & Privacy Notes
# Sensitive ops (if any). Stays local unless explicit user consent for publishing evidence.

# ===
# ===
# ===
Write-Host "=== Open-DARF · Windows installer with heartbeat ==="

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

try {
  if (-not (Get-Command docker -ErrorAction SilentlyContinue)) { throw "Docker Desktop not found." }
  Set-Location -Path "$PSScriptRoot\.."
  docker compose config | Out-Null

  Write-Host "[1] Launching core databases…"
  Start-Heartbeat "Starting containers"
  docker compose up -d minio neo4j qdrant postgres
  Stop-Heartbeat

  Write-Host "[2] Waiting for services…"
  Start-Heartbeat "Probing MinIO"
  1..30 | ForEach-Object { try { curl.exe -fsS http://localhost:9000/minio/health/live | Out-Null; throw 'OK' } catch { Start-Sleep -Seconds 2 } }
} catch { if ($_.Exception.Message -eq 'OK') {} else { Stop-Heartbeat; throw } }
Stop-Heartbeat

Start-Heartbeat "Probing Qdrant"
$ok = $false
foreach ($i in 1..45) { try { curl.exe -fsS http://localhost:6333/healthz | Out-Null; $ok=$true; break } catch { Start-Sleep -Seconds 2 } }
Stop-Heartbeat

Start-Heartbeat "Probing Neo4j"
$ok2 = $false
foreach ($i in 1..60) { try { curl.exe -fsSI http://localhost:7474 | Out-Null; $ok2=$true; break } catch { Start-Sleep -Seconds 2 } }
Stop-Heartbeat

Write-Host "[✓] Databases up. Start engine with: docker compose up -d darf-engine"
