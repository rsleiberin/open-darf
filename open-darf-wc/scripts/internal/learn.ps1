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
