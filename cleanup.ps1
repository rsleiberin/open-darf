#Requires -Version 5.1
<#
.SYNOPSIS
    Open-DARF Cleanup Entry Point (Windows)
.DESCRIPTION
    Entry point for Windows PowerShell cleanup.
    Delegates to scripts/core/cleanup.ps1
.PARAMETER KeepVolumes
    If specified, preserves data volumes
.EXAMPLE
    .\cleanup.ps1
    .\cleanup.ps1 -KeepVolumes
#>

[CmdletBinding()]
param(
    [Parameter()]
    [switch]$KeepVolumes
)

$ErrorActionPreference = "Stop"
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path

# Execute core cleanup
$coreCleanup = Join-Path $scriptDir "scripts\core\cleanup.ps1"
if (-not (Test-Path $coreCleanup)) {
    Write-Host "ERROR: Core cleanup script not found at: $coreCleanup" -ForegroundColor Red
    exit 1
}

if ($KeepVolumes) {
    & $coreCleanup -KeepVolumes
} else {
    & $coreCleanup
}
exit $LASTEXITCODE
