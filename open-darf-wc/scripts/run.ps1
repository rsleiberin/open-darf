# ===
# ===
# ===
Write-Host "=== Open-DARF · One-line (Windows) — compose DB + clean Neo4j + evidence ==="
function Start-Heartbeat([string]$Msg){ if ($script:hb){$script:hb.Stop();$script:hb.Dispose()}; $script:hb=New-Object System.Timers.Timer; $script:hb.Interval=2000; $script:hb.AutoReset=$true; $script:hb.add_Elapsed({Write-Host "[HB] $Msg — $(Get-Date -Format HH:mm:ss)"}); $script:hb.Start() }
function Stop-Heartbeat { if ($script:hb){$script:hb.Stop();$script:hb.Dispose();$script:hb=$null} }

Set-Location -Path "$PSScriptRoot\.."

# Compose DB
Start-Heartbeat "compose up -d (DB)"
docker compose up -d minio qdrant postgres
Stop-Heartbeat

# Clean Neo4j
docker ps -aq --filter "name=^darf-neo4j$" | ForEach-Object { docker rm -f $_ } | Out-Null
docker volume create open-darf_neo4j_data | Out-Null
docker volume create open-darf_neo4j_logs | Out-Null
Start-Heartbeat "docker run neo4j clean"
docker run -d --name darf-neo4j --network open-darf_default --network-alias neo4j `
  -p 7474:7474 -p 7687:7687 `
  -v open-darf_neo4j_data:/data -v open-darf_neo4j_logs:/logs `
  -e NEO4J_AUTH=$( $env:NEO4J_USERNAME + '/' + $env:NEO4J_PASSWORD ) neo4j:5.15-community | Out-Null
Stop-Heartbeat

# Bounded probe
$ok=$false
for ($i=1; $i -le 15; $i++){ Start-Heartbeat "neo4j bolt probe $i/15"; if (docker exec darf-neo4j cypher-shell -u neo4j -p darf_graph_password "RETURN 1;" 2>$null){ $ok=$true; break } Start-Sleep -Seconds 2; Stop-Heartbeat }
Stop-Heartbeat

# Evidence pack
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\evidence_pack.ps1
