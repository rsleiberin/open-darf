# ===
# ===
# ===
Write-Host "=== Open-DARF · Evidence Pack (Windows, heartbeat, cancel-safe) ==="

function Start-Heartbeat([string]$Msg) {
  if ($script:hb) { Stop-Heartbeat }
  $script:hb = New-Object System.Timers.Timer
  $script:hb.Interval = 2000; $script:hb.AutoReset = $true
  $script:hb.add_Elapsed({ Write-Host "[HB] $Msg — $(Get-Date -Format HH:mm:ss)" })
  $script:hb.Start()
}
function Stop-Heartbeat {
  if ($script:hb) { $script:hb.Stop(); $script:hb.Dispose(); $script:hb = $null }
}

$root = Split-Path -Parent $MyInvocation.MyCommand.Path | Split-Path -Parent
$results = Join-Path $root "results"
New-Item -ItemType Directory -Force -Path $results | Out-Null

$outdir = "evidence_$($env:COMPUTERNAME)_$(Get-Date -Format 'yyyyMMddTHHmmss')"
$work = Join-Path $results $outdir
New-Item -ItemType Directory -Force -Path $work | Out-Null

$services = @('darf-minio','darf-qdrant','darf-postgres','darf-neo4j')

Start-Heartbeat "Collecting docker state"
docker ps --format '{{.ID}}\t{{.Image}}\t{{.Names}}\t{{.Status}}\t{{.Ports}}' | Out-File -Encoding utf8 (Join-Path $work 'docker_ps.tsv')
docker images --digests --format '{{.Repository}}\t{{.Tag}}\t{{.ID}}\t{{.Digest}}' | Out-File -Encoding utf8 (Join-Path $work 'docker_images.tsv')
Stop-Heartbeat

# Health
Start-Heartbeat "Health checks"
try { (curl.exe -fsS http://localhost:9000/minio/health/live) | Out-File -Encoding utf8 (Join-Path $work 'minio_health.txt') } catch { "fail" | Out-File (Join-Path $work 'minio_health.txt') }
try { (curl.exe -fsS http://localhost:6333/healthz) | Out-File -Encoding utf8 (Join-Path $work 'qdrant_health.txt') } catch { "fail" | Out-File (Join-Path $work 'qdrant_health.txt') }
try { docker exec darf-postgres pg_isready -U darf_user -d darf_audit | Out-File -Encoding utf8 (Join-Path $work 'pg_ready.txt') } catch { "fail" | Out-File (Join-Path $work 'pg_ready.txt') }
$neo = "fail"
$sw = [System.Diagnostics.Stopwatch]::StartNew()
if (docker exec darf-neo4j cypher-shell -u neo4j -p darf_graph_password "RETURN 1;" 2>$null) { $sw.Stop(); $neo = "ok $($sw.ElapsedMilliseconds)ms" } else { $sw.Stop() }
$neo | Out-File -Encoding utf8 (Join-Path $work 'neo4j_bolt.txt')
Stop-Heartbeat

# Logs
foreach ($s in $services) { try { docker logs --tail 200 $s | Out-File -Encoding utf8 (Join-Path $work "$s`_logs_tail.txt") } catch {} }

# Compose + receipts
Copy-Item (Join-Path $root 'docker-compose.yml') -Destination $work -ErrorAction SilentlyContinue
Copy-Item (Join-Path $root 'docker-compose.override.yml') -Destination $work -ErrorAction SilentlyContinue
Get-ChildItem $results -Filter *.json -ErrorAction SilentlyContinue | Copy-Item -Destination $work

# Manifest
@{
  ts = (Get-Date).ToString('s')
  host = $env:COMPUTERNAME
  os = (Get-CimInstance Win32_OperatingSystem).Caption
  docker = (docker --version)
} | ConvertTo-Json | Out-File -Encoding utf8 (Join-Path $work 'MANIFEST.json')

# Archive
$zip = Join-Path $results "$outdir.zip"
if (Test-Path $zip) { Remove-Item $zip -Force }
Compress-Archive -Path (Join-Path $work '*') -DestinationPath $zip
Write-Host "[✓] Evidence archive: $zip"
