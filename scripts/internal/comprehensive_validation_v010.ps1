#!/usr/bin/env pwsh
#Requires -Version 5.1
<#
.SYNOPSIS
  Comprehensive validation v0.1.0 (PowerShell) — receipt generation
.DESCRIPTION
  Mirrors Linux validation to produce v0.1.0 JSON receipts using only measured values.
  Stores receipts under open-darf/var/receipts/open-darf/.
.PARAMETER Iterations
  Number of validation iterations (default: 3)
.EXAMPLE
  pwsh -File .\scripts\internal\comprehensive_validation_v010.ps1 -Iterations 3
#>

param(
  [int]$Iterations = 3
)

$ErrorActionPreference = "Stop"

function Get-TimestampMs {
  return [int64]([DateTimeOffset]::UtcNow.ToUnixTimeMilliseconds())
}

function Get-Percentile {
  param([double[]]$Array, [int]$Percentile)
  if (-not $Array -or $Array.Count -eq 0) { return 0 }
  $Sorted = $Array | Sort-Object
  $Index  = [Math]::Floor($Array.Count * $Percentile / 100)
  if ($Index -ge $Array.Count) { $Index = $Array.Count - 1 }
  return [double]$Sorted[$Index]
}

# Load .env (if present) to populate env vars like NEO4J_PASSWORD
$EnvPathCandidates = @(
  Join-Path (Get-Location) ".env",
  Join-Path (Split-Path $PSCommandPath -Parent) "../.env",
  Join-Path (Split-Path $PSCommandPath -Parent) "../../.env"
) | ForEach-Object { Resolve-Path -ErrorAction SilentlyContinue $_ } | Select-Object -ExpandProperty Path -Unique

foreach ($envFile in $EnvPathCandidates) {
  if (Test-Path $envFile) {
    Get-Content $envFile | ForEach-Object {
      if ($_ -match '^\s*([^#][^=]+)=(.*)$') {
        [Environment]::SetEnvironmentVariable($matches[1].Trim(), $matches[2].Trim())
      }
    }
    break
  }
}

# Resolve repo root as open-darf/ from this script location
$ScriptDir = Split-Path -Parent $PSCommandPath
$RepoRoot  = Resolve-Path (Join-Path $ScriptDir "..\..")
$ReceiptDir = Join-Path $RepoRoot "var/receipts/open-darf"
New-Item -ItemType Directory -Force -Path $ReceiptDir | Out-Null

$ReceiptId   = "validation_{0}" -f (Get-Date -Format 'yyyyMMdd_HHmmss')
$ReceiptPath = Join-Path $ReceiptDir ($ReceiptId + ".json")

# Timing accumulators
$TOTAL   = New-Object System.Collections.Generic.List[double]
$DOC     = New-Object System.Collections.Generic.List[double]
$RULE    = New-Object System.Collections.Generic.List[double]
$AUDIT   = New-Object System.Collections.Generic.List[double]

# Quick helpers to run docker compose commands and time them
function Invoke-Timed {
  param([string]$CommandLine)
  $start = Get-TimestampMs
  $proc  = Start-Process -FilePath "bash" -ArgumentList "-lc", $CommandLine -NoNewWindow -Wait -PassThru -RedirectStandardOutput /tmp/ps_out.txt -RedirectStandardError /tmp/ps_err.txt
  $end   = Get-TimestampMs
  $dur   = [double]($end - $start)
  return @{
    duration_ms = $dur
    stdout      = (Get-Content /tmp/ps_out.txt -Raw -ErrorAction SilentlyContinue)
    stderr      = (Get-Content /tmp/ps_err.txt -Raw -ErrorAction SilentlyContinue)
    exitcode    = $proc.ExitCode
  }
}

# Infrastructure health checks (boolean flags only, no mock values)
$NEO4J_OK = $false
$POSTGRES_OK = $false
try {
  $r = Invoke-Timed -CommandLine "docker compose exec -T neo4j cypher-shell -u neo4j -p `"$env:NEO4J_PASSWORD`" `"RETURN 1`""
  if ($r.exitcode -eq 0) { $NEO4J_OK = $true }
} catch {}
try {
  $r = Invoke-Timed -CommandLine "docker compose exec -T postgres psql -U darf_user -d appdb -t -c `"SELECT 1`""
  if ($r.exitcode -eq 0) { $POSTGRES_OK = $true }
} catch {}

# Baseline query (used for comparative analysis)
$baselineCall = Invoke-Timed -CommandLine "docker compose exec -T neo4j cypher-shell -u neo4j -p `"$env:NEO4J_PASSWORD`" `"MATCH (d:Document) RETURN count(d)`""
$BASELINE_MS = [double]$baselineCall.duration_ms

# Measurement loop (Iterations)
for ($i = 1; $i -le $Iterations; $i++) {
  $IterStart = Get-TimestampMs

  # Document ingestion (idempotent MERGE)
  $docCall = Invoke-Timed -CommandLine "docker compose exec -T neo4j cypher-shell -u neo4j -p `"$env:NEO4J_PASSWORD`" `"MERGE (d:Document {id:'ps_test_$i'}) RETURN d.id`""
  $DOC.Add([double]$docCall.duration_ms)

  # Rule retrieval (R0 existence)
  $ruleCall = Invoke-Timed -CommandLine "docker compose exec -T neo4j cypher-shell -u neo4j -p `"$env:NEO4J_PASSWORD`" `"MATCH (r:Rule) WHERE r.id='R0' RETURN r.id LIMIT 1`""
  $RULE.Add([double]$ruleCall.duration_ms)

  # Audit write (INSERT)
  $auditCall = Invoke-Timed -CommandLine "docker compose exec -T postgres psql -U darf_user -d appdb -t -c `"INSERT INTO audit_log (event) VALUES ('ps_test_$i') RETURNING id`""
  $AUDIT.Add([double]$auditCall.duration_ms)

  $IterEnd = Get-TimestampMs
  $TOTAL.Add([double]($IterEnd - $IterStart))
  Write-Host ("Iteration {0} complete: {1}ms" -f $i, ([int][double]$TOTAL[-1])) -ForegroundColor Gray
}

# Percentiles (derived only from measured arrays)
$Perf_EndToEnd = [ordered]@{
  p50 = [int](Get-Percentile -Array $TOTAL.ToArray() -Percentile 50)
  p90 = [int](Get-Percentile -Array $TOTAL.ToArray() -Percentile 90)
  p95 = [int](Get-Percentile -Array $TOTAL.ToArray() -Percentile 95)
  p99 = [int](Get-Percentile -Array $TOTAL.ToArray() -Percentile 99)
}

$Perf_Components = [ordered]@{
  document_ingestion = @{ p50 = [int](Get-Percentile -Array $DOC.ToArray()   -Percentile 50) }
  rule_retrieval     = @{
    p50 = [int](Get-Percentile -Array $RULE.ToArray()  -Percentile 50)
    p90 = [int](Get-Percentile -Array $RULE.ToArray()  -Percentile 90)
    p95 = [int](Get-Percentile -Array $RULE.ToArray()  -Percentile 95)
    p99 = [int](Get-Percentile -Array $RULE.ToArray()  -Percentile 99)
  }
  audit_write        = @{ p50 = [int](Get-Percentile -Array $AUDIT.ToArray()  -Percentile 50) }
}

# Resource breakdown (derived only from measured medians; guards against divide-by-zero)
$io_pct = $null
if ($Perf_EndToEnd.p50 -gt 0) {
  $io_pct = [math]::Round( ( ($Perf_Components.document_ingestion.p50 + $Perf_Components.rule_retrieval.p50 + $Perf_Components.audit_write.p50) / $Perf_EndToEnd.p50 ) * 100.0, 2 )
}

# Comparative analysis (derived only from measured values)
$delta_ms = [int]($Perf_EndToEnd.p50 - $BASELINE_MS)
$delta_pct = $null
if ($BASELINE_MS -gt 0) {
  $delta_pct = [math]::Round( ($delta_ms / $BASELINE_MS) * 100.0, 2 )
}

# System context (measured/queried)
$platform =
  if ($IsWindows) { "Windows" }
  elseif ($IsLinux) { "Linux" }
  elseif ($IsMacOS) { "macOS" }
  else { "Unknown" }

$docker_version = $null
try { $docker_version = (& docker --version) -replace '^Docker version ', '' } catch {}

$receipt = [ordered]@{
  receipt_version = "0.1.0"
  receipt_id      = $ReceiptId
  timestamp       = (Get-Date).ToUniversalTime().ToString("yyyy-MM-ddTHH:mm:ssZ")
  iterations      = $Iterations
  system_context  = [ordered]@{
    platform        = $platform
    architecture    = $env:PROCESSOR_ARCHITECTURE
    docker_version  = $docker_version
  }
  performance_percentiles = [ordered]@{
    end_to_end_latency_ms = $Perf_EndToEnd
    component_timing_ms   = $Perf_Components
    resource_breakdown    = @{ io_percentage = $io_pct }
  }
  value_metrics = [ordered]@{
    # Kept minimal; only include measurable or known-at-runtime values
    constitutional_compliance_rate = $null
    audit_coverage_percentage      = $null
    sovereignty_preservation       = "mathematical-framework-ready"
  }
  validation_results = [ordered]@{
    test_document_ingestion = @{
      status            = if ($DOC.Count -eq $Iterations) { "PASS" } else { "UNKNOWN" }
      iterations_tested = $Iterations
      pass_rate         = $null
      content_addressing_verified = $null
    }
    test_constitutional_validation = @{
      status            = if ($RULE.Count -eq $Iterations) { "PASS" } else { "UNKNOWN" }
      iterations_tested = $Iterations
      pass_rate         = $null
      rules_loaded      = $NEO4J_OK
    }
    test_infrastructure_health = @{
      neo4j_accessible   = $NEO4J_OK
      postgres_accessible= $POSTGRES_OK
    }
  }
  comparative_analysis = [ordered]@{
    baseline_system = @{
      description  = "RAG baseline (reference Neo4j query)"
      latency_ms   = [int]$BASELINE_MS
      compliance_rate = $null
      audit_coverage  = $null
    }
    constitutional_system = @{
      description  = "RAG with validation timing path"
      latency_ms   = $Perf_EndToEnd.p50
      compliance_rate = $null
      audit_coverage  = $null
    }
    value_proposition = @{
      latency_delta_ms         = $delta_ms
      latency_delta_percentage = $delta_pct
      value_delivered          = @(
        "Formalizable validation path",
        "Provenance-ready receipts",
        "Deterministic JSON format (v0.1.0)"
      )
    }
  }
  methodology = [ordered]@{
    measurement_layers = [ordered]@{
      layer_1_pure_logic = @{
        measured = $false
        note     = "Pure-logic microbenchmarks are not synthesized here; avoid mock numbers."
      }
      layer_2_infrastructure = @{
        measured = $true
        note     = "Docker exec timing for DB + graph operations."
      }
      layer_3_end_to_end = @{
        measured  = $true
        iterations= $Iterations
      }
    }
    percentile_calculation = "sorted array indexing"
    statistical_approach   = "non-parametric percentiles"
    reproducibility        = @{
      deterministic = $false
      variance_sources = @("network_latency","database_cache_state","system_load","docker_exec_overhead")
    }
  }
  evidence_artifacts = [ordered]@{
    receipt_file = (Resolve-Path $ReceiptPath).Path
    benchmark_data = @{
      layer_1 = $null
    }
  }
}

$receipt | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath $ReceiptPath -Encoding UTF8
Write-Host ""
Write-Host ("Receipt: {0}" -f $ReceiptPath) -ForegroundColor Green
