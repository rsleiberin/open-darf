#!/usr/bin/env python3
import sys, json, os, time

import os, time, json, hashlib, statistics
import torch  # type: ignore

def artifact_hash(path):
    h=hashlib.sha256()
    with open(path,"rb") as f: h.update(f.read())
    return h.hexdigest()

TS=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
OUTDIR=os.path.join("var","receipts",TS)
os.makedirs(OUTDIR, exist_ok=True)

result={"system":{}, "timing":{}, "result":{}, "artifact_hash": None}
result["system"]={
  "gpu_name": torch.cuda.get_device_name(0) if torch.cuda.is_available() else "NA",
  "driver": os.popen("nvidia-smi --query-gpu=driver_version --format=csv,noheader 2>/dev/null").read().strip() or "NA",
  "cuda_driver": os.popen("nvidia-smi --query-gpu=compute_cap --format=csv,noheader 2>/dev/null").read().strip() or "NA",
  "torch_version": torch.__version__,
  "torch_cuda": getattr(torch.version,cuda,None),
}

# Deterministic micro workload
if not torch.cuda.is_available():
    passed=False
    reason="torch.cuda.is_available()==False"
    p50=p95=float("inf")
else:
    dev="cuda:0"
    torch.manual_seed(42)
    iters=2000
    warmup=500
    x=torch.randn((1024,1024), device=dev)
    y=torch.randn((1024,1024), device=dev)
    times=[]
    torch.cuda.synchronize()
    for _ in range(warmup):
        z = torch.add(x,y)
    torch.cuda.synchronize()
    for _ in range(iters):
        t0=time.perf_counter()
        z = torch.add(x,y, alpha=1.0)
        torch.cuda.synchronize()
        t1=time.perf_counter()
        times.append((t1-t0)*1000.0)
    p50 = statistics.median(times)
    p95 = sorted(times)[int(0.95*len(times))-1]
    # Conservative pass bar for heterogenous peers (tune later)
    passed = p95 < 1.5  # ms
    reason = None if passed else f"p95={p95:.3f}ms exceeds threshold"

result["timing"]={"p50_ms": round(p50,4) if p50!=float("inf") else None,
                  "p95_ms": round(p95,4) if p95!=float("inf") else None,
                  "n_iters": 2000}
result["result"]={"passed": bool(passed), "reason": reason}
result["artifact_hash"]=artifact_hash(__file__)

with open(os.path.join(OUTDIR,"validator_summary.json"),"w") as f: json.dump(result,f,indent=2,sort_keys=True)
with open(os.path.join(OUTDIR,"system_snapshot.json"),"w") as f: json.dump(result["system"],f,indent=2,sort_keys=True)
with open(os.path.join(OUTDIR,"console.log"),"w") as f: f.write(json.dumps({"note":"minimal validator run complete"}, indent=2))
print(json.dumps(result, indent=2))
