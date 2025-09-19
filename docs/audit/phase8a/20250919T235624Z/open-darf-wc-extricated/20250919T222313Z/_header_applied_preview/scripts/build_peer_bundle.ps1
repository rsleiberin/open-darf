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
Write-Host "=== Open-DARF · Build Peer Bundle (Windows) ==="
$root = Split-Path -Parent $MyInvocation.MyCommand.Path | Split-Path -Parent
$out  = Join-Path $root "results\bundles"
New-Item -ItemType Directory -Force -Path $out | Out-Null

$stamp = Get-Date -Format 'yyyyMMddTHHmmss'
$tmp   = Join-Path $root ("results\_bundle_{0}" -f $stamp)
New-Item -ItemType Directory -Force -Path (Join-Path $tmp 'scripts') | Out-Null
New-Item -ItemType Directory -Force -Path (Join-Path $tmp 'docs')    | Out-Null

Copy-Item (Join-Path $root 'scripts\run.ps1')                       (Join-Path $tmp 'scripts') -Force
Copy-Item (Join-Path $root 'scripts\validator_acceptance.ps1')      (Join-Path $tmp 'scripts') -Force
Copy-Item (Join-Path $root 'scripts\kill_switch.ps1')               (Join-Path $tmp 'scripts') -Force -ErrorAction SilentlyContinue
Copy-Item (Join-Path $root 'scripts\run.sh')                        (Join-Path $tmp 'scripts') -Force
Copy-Item (Join-Path $root 'scripts\validator_acceptance.sh')       (Join-Path $tmp 'scripts') -Force
Copy-Item (Join-Path $root 'scripts\kill_switch.sh')                (Join-Path $tmp 'scripts') -Force -ErrorAction SilentlyContinue
Copy-Item (Join-Path $root 'scripts\check_ports.sh')                (Join-Path $tmp 'scripts') -Force -ErrorAction SilentlyContinue
Copy-Item (Join-Path $root 'scripts\install_and_run.ps1')           (Join-Path $tmp 'scripts') -Force -ErrorAction SilentlyContinue
Copy-Item (Join-Path $root 'scripts\install_and_run.sh')            (Join-Path $tmp 'scripts') -Force -ErrorAction SilentlyContinue
Copy-Item (Join-Path $root 'README.md')                             $tmp -Force
Copy-Item (Join-Path $root 'docs\peer_validator_onboarding.md')     (Join-Path $tmp 'docs') -Force -ErrorAction SilentlyContinue
Copy-Item (Join-Path $root 'docs\compose_vs_bare_neo4j.md')         (Join-Path $tmp 'docs') -Force -ErrorAction SilentlyContinue

'Write-Host "=== Open-DARF · Start (Windows) ==="
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1' |
  Out-File -Encoding utf8 (Join-Path $tmp 'START_WINDOWS.ps1')

'#!/usr/bin/env bash
set -euo pipefail
printf "===`n===`n===`n"
echo "=== Open-DARF · Start (Linux) ==="
bash ./scripts/run.sh' |
  Out-File -Encoding utf8 (Join-Path $tmp 'start_linux.sh')

$basename = "open-darf-peer-bundle_{0}.zip" -f $stamp
$zipPath  = Join-Path $out $basename
if (Test-Path $zipPath) { Remove-Item $zipPath -Force }
Compress-Archive -Path (Join-Path $tmp '*') -DestinationPath $zipPath
Write-Host ("[✓] Bundle: {0}" -f $zipPath)
