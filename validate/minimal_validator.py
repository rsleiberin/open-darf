#!/usr/bin/env python3
import os, sys, time, json, hashlib, statistics, math, subprocess

TS = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
OUTDIR = os.environ.get("VALIDATOR_OUTDIR")
if not OUTDIR:
    TS = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    OUTDIR = os.path.join("var","receipts", TS + "_validator")
os.makedirs(OUTDIR, exist_ok=True)
os.makedirs(OUTDIR, exist_ok=True)

def artifact_hash(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        h.update(f.read())
    return h.hexdigest()

def run(cmd):
    try:
        out = subprocess.check_output(cmd, stderr=subprocess.DEVNULL, text=True)
        return out.strip()
    except Exception:
        return ""

# Environment signals
kernel_rel = run(["uname","-r"]).lower()
is_wsl = ("wsl" in kernel_rel) or os.path.exists("/run/WSL") or "microsoft" in kernel_rel

# GPU signals via nvidia-smi (may exist under WSL but without /dev/nvidia*)
nvsmi_name_drv = run(["bash","-lc","nvidia-smi --query-gpu=name,driver_version --format=csv,noheader 2>/dev/null | head -n1"])
gpu_name = "NA"
driver = "NA"
if nvsmi_name_drv:
    parts = [p.strip() for p in nvsmi_name_drv.split(",")]
    if parts:
        gpu_name = parts[0]
    if len(parts) > 1:
        driver = parts[1]

cuda_driver = "NA"
if os.path.exists("/usr/lib/wsl/lib/libcuda.so.1"):
    cuda_driver = "wsl_proxy"
elif os.path.exists("/usr/lib/x86_64-linux-gnu/libcuda.so.1"):
    cuda_driver = "native"

system = {
    "gpu_name": gpu_name,
    "driver": driver,
    "cuda_driver": cuda_driver,
    "torch_version": "not_imported",
    "torch_cuda": None,
}

# Try torch import
torch = None
reason = None
passed = False
p50 = None
p95 = None
iters = 0

try:
    import torch as _torch
    torch = _torch
    system["torch_version"] = torch.__version__
    system["torch_cuda"] = getattr(torch.version, "cuda", None)
except Exception as e:
    reason = f"torch import failed: {type(e).__name__}"

if torch is None:
    # Write receipts and exit cleanly
    summary = {
        "system": system,
        "timing": {"p50_ms": None, "p95_ms": None, "n_iters": 0},
        "result": {"passed": False, "reason": reason or "torch not installed"},
        "artifact_hash": artifact_hash(__file__),
    }
    with open(os.path.join(OUTDIR,"validator_summary.json"),"w") as f: json.dump(summary,f,indent=2,sort_keys=True)
    with open(os.path.join(OUTDIR,"system_snapshot.json"),"w") as f: json.dump(system,f,indent=2,sort_keys=True)
    with open(os.path.join(OUTDIR,"console.log"),"w") as f: f.write("validator: torch missing or failed to import\n")
    print(json.dumps(summary, indent=2))
    # Non-zero to indicate validator didn't pass; runner script will continue
    sys.exit(7)

# Torch present; check CUDA availability
if not torch.cuda.is_available():
    reason = "torch.cuda.is_available()==False"
    if is_wsl:
        reason += " (WSL environment; /dev/nvidia* absent)"
else:
    # Deterministic small workload
    dev = "cuda:0"
    torch.manual_seed(42)
    warmup = 500
    iters = 2000
    x = torch.randn((1024,1024), device=dev)
    y = torch.randn((1024,1024), device=dev)
    torch.cuda.synchronize()
    for _ in range(warmup):
        _ = torch.add(x, y, alpha=1.0)
    torch.cuda.synchronize()
    times = []
    for _ in range(iters):
        t0 = time.perf_counter()
        _ = torch.add(x, y, alpha=1.0)
        torch.cuda.synchronize()
        t1 = time.perf_counter()
        times.append((t1 - t0) * 1000.0)
    p50 = statistics.median(times)
    p95 = sorted(times)[int(math.ceil(0.95*len(times))) - 1]
    # Conservative placeholder threshold; to be tuned with native runs
    passed = p95 < 1.5
    if not passed:
        reason = f"p95={p95:.3f}ms exceeds threshold"

summary = {
    "system": system,
    "timing": {"p50_ms": round(p50,4) if p50 is not None else None,
               "p95_ms": round(p95,4) if p95 is not None else None,
               "n_iters": iters},
    "result": {"passed": bool(passed), "reason": reason},
    "artifact_hash": artifact_hash(__file__),
}

with open(os.path.join(OUTDIR,"validator_summary.json"),"w") as f: json.dump(summary,f,indent=2,sort_keys=True)
with open(os.path.join(OUTDIR,"system_snapshot.json"),"w") as f: json.dump(system,f,indent=2,sort_keys=True)
with open(os.path.join(OUTDIR,"console.log"),"w") as f: f.write("validator: completed\n")

print(json.dumps(summary, indent=2))
# Exit 0 on pass, 8 on fail so upstream can record rc
sys.exit(0 if passed else 8)
