# Constitutional validation engine for open-darf (PowerShell)
param()

$ErrorActionPreference = "Stop"

function Get-Timestamp { [DateTime]::UtcNow.ToString("yyyy-MM-ddTHH:mm:ssZ") }
function Get-Milliseconds { [int64]([DateTimeOffset]::UtcNow.ToUnixTimeMilliseconds()) }

# Load environment variables
if (Test-Path .env) {
    Get-Content .env | ForEach-Object {
        if ($_ -match '^\s*([^#][^=]+)=(.*)$') {
            $name = $matches[1].Trim()
            $value = $matches[2].Trim()
            [Environment]::SetEnvironmentVariable($name, $value, "Process")
        }
    }
}

# Validation context
$CTX_IRREVERSIBLE = if ($env:CTX_IRREVERSIBLE) { $env:CTX_IRREVERSIBLE } else { "true" }
$CTX_HAS_REVIEW = if ($env:CTX_HAS_REVIEW) { $env:CTX_HAS_REVIEW } else { "false" }
$CTX_ACTOR = if ($env:CTX_ACTOR) { $env:CTX_ACTOR } else { "peer_validator" }
$CTX_ACTION = if ($env:CTX_ACTION) { $env:CTX_ACTION } else { "validation_run" }

# Generate validation ID and timestamp
$VALIDATION_ID = [guid]::NewGuid().ToString()
$TIMESTAMP = Get-Timestamp

# Query Neo4j for rule R0
$neo_start = Get-Milliseconds
try {
    $ruleOutput = docker compose exec -T neo4j cypher-shell -u neo4j -p "$env:NEO4J_PASSWORD" "MATCH (r:Rule {id:'R0'}) RETURN r.requires_review_for_irreversible, r.priority" 2>$null
    $ruleLines = $ruleOutput -split "`n" | Select-Object -Skip 1
    $ruleData = $ruleLines[0] -split '\s+'
    $REQ = $ruleData[0]
    $PRI = $ruleData[1] -replace '"', ''
} catch {
    $REQ = "false"
    $PRI = "unknown"
}
$neo_ms = Get-Milliseconds - $neo_start

# Apply tri-state logic with DENY precedence
$DECISION = "INDETERMINATE"
$REASON = "no_applicable_rule"

if ($REQ -eq "true" -and $CTX_IRREVERSIBLE -eq "true" -and $CTX_HAS_REVIEW -ne "true") {
    $DECISION = "DENY"
    $REASON = "irreversible_action_without_required_review"
} elseif ($CTX_IRREVERSIBLE -eq "false") {
    $DECISION = "ALLOW"
    $REASON = "action_is_reversible"
}

# Store audit receipt in PostgreSQL
$postgres_start = Get-Milliseconds
$DETAILS_JSON = @"
{"rule_id":"R0","reason":"$REASON","context":{"actor":"$CTX_ACTOR","action":"$CTX_ACTION","irreversible":$CTX_IRREVERSIBLE,"has_review":$CTX_HAS_REVIEW},"neo4j_ms":$neo_ms}
"@

try {
    docker compose exec -T -e PGPASSWORD="$env:POSTGRES_PASSWORD" postgres psql -U "$env:POSTGRES_USER" -d "$env:POSTGRES_DB" -v ON_ERROR_STOP=1 -c "INSERT INTO audit.receipts(component, action, status, details, duration_ms) VALUES ('constitutional_engine', '$CTX_ACTION', '$DECISION', '$DETAILS_JSON'::jsonb, $neo_ms)" 2>$null | Out-Null
} catch {
    # Continue even if audit insert fails
}
$postgres_ms = Get-Milliseconds - $postgres_start
$total_ms = $neo_ms + $postgres_ms

# Collect system fingerprint
$OS = [System.Environment]::OSVersion.Platform
$CPU_CORES = (Get-WmiObject Win32_ComputerSystem).NumberOfLogicalProcessors
$RAM_GB = [math]::Round((Get-WmiObject Win32_ComputerSystem).TotalPhysicalMemory/1GB, 2)
$DOCKER_VERSION = (docker --version) -replace '.*version ([0-9.]+).*', '$1'

# Output JSON result
@{
    receipt_version = "1.0"
    engine_version = "constitutional-v3"
    validation_id = $VALIDATION_ID
    timestamp = $TIMESTAMP
    decision = $DECISION
    reason = $REASON
    context = @{
        actor = $CTX_ACTOR
        action = $CTX_ACTION
        irreversible = [bool]::Parse($CTX_IRREVERSIBLE)
        has_review = [bool]::Parse($CTX_HAS_REVIEW)
    }
    performance = @{
        neo4j_query_ms = $neo_ms
        postgres_write_ms = $postgres_ms
        total_ms = $total_ms
    }
    system_context = @{
        platform = $OS.ToString()
        cpu_cores = $CPU_CORES
        ram_gb = $RAM_GB
        docker_version = $DOCKER_VERSION
    }
} | ConvertTo-Json -Depth 10
