#Requires -Version 5.1
<#
.SYNOPSIS
    Open-DARF Installation Entry Point (Windows)
.DESCRIPTION
    Entry point for Windows PowerShell installation.
    Delegates to scripts/core/install.ps1
.EXAMPLE
    .\install.ps1
#>

[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path

# Run preflight checks if available
$preflightScript = Join-Path $scriptDir "scripts\internal\preflight_public.ps1"
if (Test-Path $preflightScript) {
    Write-Host "Running preflight checks..." -ForegroundColor Cyan
    & $preflightScript
}

# Execute core installation
$coreInstall = Join-Path $scriptDir "scripts\core\install.ps1"
if (-not (Test-Path $coreInstall)) {
    Write-Host "ERROR: Core installation script not found at: $coreInstall" -ForegroundColor Red
    exit 1
}

& $coreInstall
exit $LASTEXITCODE
