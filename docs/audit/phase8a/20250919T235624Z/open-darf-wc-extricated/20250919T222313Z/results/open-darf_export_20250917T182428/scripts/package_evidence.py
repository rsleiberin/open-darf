#!/usr/bin/env python3
import tarfile, time, os
from pathlib import Path

root = Path(__file__).resolve().parent.parent
out = root / "grant_evidence_package.tar.gz"

members = []
def maybe_add(p):
    p = Path(p)
    if p.exists():
        members.append(p)

# Core files and directories
for p in [
    "README.md",
    "docs/CONSTITUTIONAL_FRAMEWORK.md",
    "docs/METHODOLOGY.md",
    "docs/PERFORMANCE_ANALYSIS.md",
    "results/summary.json",
    "results/performance_metrics.json",
    "results/constitutional_decisions.json",
    "results/health_report.json",
    "docker-compose.yml",
    "docker-compose.override.yml"
]:
    maybe_add(root / p)

# Create tarball
with tarfile.open(out, "w:gz") as tar:
    for m in members:
        tar.add(m, arcname=str(m.relative_to(root)))
print(f"Wrote {out} ({len(members)} files) at {time.ctime()}")
