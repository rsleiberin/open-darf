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
Write-Host "=== Open-DARF · Validator Acceptance (Windows) ==="

function Start-Heartbeat([string]$Msg){ if ($script:hb){$script:hb.Stop();$script:hb.Dispose()}; $script:hb=New-Object System.Timers.Timer; $script:hb.Interval=2000; $script:hb.AutoReset=$true; $script:hb.add_Elapsed({Write-Host "[HB] $Msg — $(Get-Date -Format HH:mm:ss)"}); $script:hb.Start() }
function Stop-Heartbeat { if ($script:hb){$script:hb.Stop();$script:hb.Dispose();$script:hb=$null} }

$root = Split-Path -Parent $MyInvocation.MyCommand.Path | Split-Path -Parent
Set-Location -Path $root
$results = Join-Path $root "results"
New-Item -ItemType Directory -Force -Path $results | Out-Null

$max = 15
$ok_minio="fail"; $ok_qdrant="fail"; $ok_pg="fail"; $ok_neo="fail"

for ($i=1; $i -le $max; $i++){
  Start-Heartbeat "acceptance $i/$max"
  try { (curl.exe -fsS http://localhost:9000/minio/health/live) *> $null; $ok_minio="ok" } catch {}
  try { (curl.exe -fsS http://localhost:6333/healthz) *> $null;             $ok_qdrant="ok" } catch {}
  try { docker exec darf-postgres pg_isready -U darf_user -d darf_audit *> $null; $ok_pg="ok" } catch {}
  try { docker exec darf-neo4j cypher-shell -u neo4j -p darf_graph_password "RETURN 1;" *> $null; $ok_neo="ok" } catch {}
  Stop-Heartbeat
  if ($ok_minio -eq "ok" -and $ok_qdrant -eq "ok" -and $ok_pg -eq "ok" -and $ok_neo -eq "ok"){ break }
}

$pass = ($ok_minio -eq "ok" -and $ok_qdrant -eq "ok" -and $ok_pg -eq "ok" -and $ok_neo -eq "ok")

Write-Host "=== Acceptance Summary ==="
Write-Host ("MinIO   : {0}" -f $ok_minio)
Write-Host ("Qdrant  : {0}" -f $ok_qdrant)
Write-Host ("Postgres: {0}" -f $ok_pg)
Write-Host ("Neo4j   : {0}" -f $ok_neo)
Write-Host ("PASS     : {0}" -f $pass)

# JSON receipt
$report = @{
  ts = (Get-Date).ToString('s')
  minio = $ok_minio
  qdrant = $ok_qdrant
  postgres = $ok_pg
  neo4j = $ok_neo
  pass = $pass
} | ConvertTo-Json
$report | Out-File -Encoding utf8 (Join-Path $results 'validator_acceptance_report_windows.json')

if (-not $pass) { exit 2 }
