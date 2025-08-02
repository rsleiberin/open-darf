#Requires -Version 5.1
<#
.SYNOPSIS
    Open-DARF Validation Entry Point (Windows)
.DESCRIPTION
    Entry point for Windows PowerShell validation.
    Delegates to scripts/core/validate.ps1
.EXAMPLE
    .\validate.ps1
#>

[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path

# Execute core validation
$coreValidate = Join-Path $scriptDir "scripts\core\validate.ps1"
if (-not (Test-Path $coreValidate)) {
    Write-Host "ERROR: Core validation script not found at: $coreValidate" -ForegroundColor Red
    exit 1
}

& $coreValidate
exit $LASTEXITCODE
