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
Write-Host "=== Open-DARF · Kill Switch & Cleanup (Windows, cancel-safe) ==="

function Start-Heartbeat([string]$Msg){ if ($script:hb){$script:hb.Stop();$script:hb.Dispose()}; $script:hb=New-Object System.Timers.Timer; $script:hb.Interval=2000; $script:hb.AutoReset=$true; $script:hb.add_Elapsed({Write-Host "[HB] $Msg — $(Get-Date -Format HH:mm:ss)"}); $script:hb.Start() }
function Stop-Heartbeat { if ($script:hb){$script:hb.Stop();$script:hb.Dispose();$script:hb=$null} }
trap { Stop-Heartbeat; Write-Host "`n[✖] Cancelled."; exit 130 }

$results = Join-Path (Split-Path -Parent $PSScriptRoot) 'results'
New-Item -ItemType Directory -Force -Path $results | Out-Null

$names = @('darf-neo4j','darf-qdrant','darf-minio','darf-postgres','darf-neo4j-1','darf-minio-1','darf-postgres-1')
$ports = @(7474,7687,6333,6334,9000,9001,5432)

Write-Host "[0] Snapshot:"
docker ps -a --format '{{.Names}}\t{{.Status}}\t{{.Ports}}' | Select-String 'darf-' | ForEach-Object { $_.ToString() }

Write-Host "[0.1] Ports:"
foreach($p in $ports){ Write-Host ("  :{0} -> " -f $p); try { & ss -ltnp "( sport = :$p )" 2>$null | Select-Object -Skip 1 } catch {} }

Write-Host "[1] Stop & remove…"
Start-Heartbeat "stopping containers"
foreach($n in $names){ try { docker stop $n *> $null } catch {}; try { docker rm $n *> $null } catch {} }
Stop-Heartbeat

Write-Host "[2] Remove compose orphans & network…"
Start-Heartbeat "compose down"
try { docker compose -f (Join-Path (Split-Path -Parent $PSScriptRoot) 'docker-compose.yml') down --remove-orphans *> $null } catch {}
Stop-Heartbeat
Start-Heartbeat "remove network"
try { docker network rm open-darf_default *> $null } catch {}
Stop-Heartbeat

Write-Host "[3] Volumes preserved (set PRUNE_VOLUMES=1 to delete via Linux kill_switch.sh)."
Write-Host "[✓] Cleanup complete."
