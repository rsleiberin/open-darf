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
Write-Host "=== Open-DARF · Learning Module (Windows) ==="
$root = Split-Path -Parent $MyInvocation.MyCommand.Path | Split-Path -Parent
$files = @('docs\learning\lesson_01_introduction.md','docs\learning\lesson_02_docker_stack.md','docs\learning\lesson_03_constitutional_ai.md')
foreach($f in $files){
  Write-Host ""
  Write-Host ("---- {0} ----" -f (Split-Path $f -Leaf))
  Get-Content (Join-Path $root $f) -TotalCount 80 | ForEach-Object { $_ -replace '^# .*','[Lesson]' } | Write-Host
}
Write-Host "`n[✓] More: open docs/learning/* in your editor."
