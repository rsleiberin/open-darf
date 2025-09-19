#!/usr/bin/env python3
import json, os, time
os.makedirs("results", exist_ok=True)
summary = {
  "generated_at": time.time(),
  "performance": {},
  "constitutional": {}
}
for name in ("performance_metrics.json", "constitutional_decisions.json"):
  p = os.path.join("results", name)
  if os.path.isfile(p):
    with open(p) as f:
      summary["performance" if "performance" in name else "constitutional"] = json.load(f)
with open("results/summary.json", "w") as f:
  json.dump(summary, f, indent=2)
print("Summary written to results/summary.json")
