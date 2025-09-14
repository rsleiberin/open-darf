#!/usr/bin/env python3
import json, sys
out = {"stage":"probe_torch_cuda"}
try:
    import torch
    out["torch_version"] = torch.__version__
    out["torch_cuda"] = getattr(torch.version, "cuda", None)
    out["cuda_available"] = bool(torch.cuda.is_available())
    out["device_count"] = torch.cuda.device_count() if out["cuda_available"] else 0
    if out["device_count"] > 0:
        p = torch.cuda.get_device_properties(0)
        out["device_0"] = {"name": p.name, "total_memory": int(p.total_memory)}
    rc = 0 if out["cuda_available"] else 6
except Exception as e:
    out["error"] = repr(e)
    rc = 5
print(json.dumps(out, indent=2))
sys.exit(rc)
