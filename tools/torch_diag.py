#!/usr/bin/env python3
import json, sys, time

def main():
    info = {"stage": "torch_diag", "notes": []}
    try:
        import torch
    except Exception as e:
        info["import_error"] = repr(e)
        info["result"] = {"passed": False, "reason": "torch not installed"}
        print(json.dumps(info, indent=2))
        # Distinct RC indicating "torch missing" (aligns with M2 expectations)
        return 5

    # Collect versions
    info["torch_version"] = getattr(torch, "__version__", "unknown")
    info["torch_cuda"] = getattr(torch.version, "cuda", None)
    cudnn_ver = getattr(getattr(torch.backends, "cudnn", None), "version", lambda: None)()
    info["cudnn_version"] = cudnn_ver

    # CUDA availability & properties
    avail = torch.cuda.is_available()
    info["cuda_available"] = bool(avail)
    info["device_count"] = torch.cuda.device_count() if avail else 0

    if avail and info["device_count"] > 0:
        props = torch.cuda.get_device_properties(0)
        info["device_0"] = {
            "name": props.name,
            "total_memory_bytes": props.total_memory,
            "cc_major": props.major,
            "cc_minor": props.minor,
        }
        # Tiny deterministic GPU op
        torch.cuda.synchronize()
        a = torch.ones((1024,1024), device="cuda")
        b = torch.ones((1024,1024), device="cuda")
        t0 = time.perf_counter()
        c = a + b
        torch.cuda.synchronize()
        dt_ms = (time.perf_counter() - t0) * 1000.0
        info["tiny_add_ms"] = round(dt_ms, 4)
        info["result"] = {"passed": True, "reason": None}
        rc = 0
    else:
        info["result"] = {"passed": False, "reason": "CUDA not available (pre-M2 expected on some hosts)"}
        rc = 6

    print(json.dumps(info, indent=2))
    return rc

if __name__ == "__main__":
    sys.exit(main())
