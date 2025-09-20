#!/usr/bin/env python3
import shutil, json, os, sys, time
report = {
  "python": sys.version.split()[0],
  "has_docker": shutil.which("docker") is not None,
  "timestamp": time.time(),
  "paths": {
    "demo_data": os.path.isdir("demo_data"),
    "results": os.path.isdir("results"),
    "docs": os.path.isdir("docs")
  }
}
os.makedirs("results", exist_ok=True)
with open("results/health_report.json", "w") as f:
  json.dump(report, f, indent=2)
print("Health check complete:", json.dumps(report))
