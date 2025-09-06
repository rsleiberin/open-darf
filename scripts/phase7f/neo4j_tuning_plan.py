#!/usr/bin/env python3
import os, json, time, pathlib, shutil
ts=time.strftime("%Y%m%d-%H%M%S", time.gmtime())
outdir=f"var/receipts/phase7f/neo4j_tuning/{ts}"
pathlib.Path(outdir).mkdir(parents=True, exist_ok=True)
mem_gb = float(os.environ.get("SYSTEM_MEM_GB","16"))
heap_gb = max(2.0, min(8.0, mem_gb*0.4))
pagecache_gb = max(1.0, min(16.0, mem_gb*0.5))
plan = {
  "phase":"7F","item":"C12","mode":"plan",
  "recommendations":{
    "server.memory.heap.max": f"{int(heap_gb)}G",
    "server.memory.pagecache.size": f"{int(pagecache_gb)}G",
    "db.tx_log.rotation.size": "256M",
    "dbms.jvm.additional": ["-XX:+UseG1GC","-XX:MaxGCPauseMillis=200"]
  },
  "applied": False,
  "notes":"Docs-only plan; apply via Neo4j config management in infra repo.",
}
with open(f"{outdir}/summary.json","w") as f: json.dump(plan, f, indent=2)
print(f"{outdir}/summary.json", end="")
