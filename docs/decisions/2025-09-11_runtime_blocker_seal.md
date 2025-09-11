# Blocker Seal — Torch CUDA fails in WSL Docker despite WSL libcuda dlopen OK

**Date:** 2025-09-11  
**Context:** Phase 7N — GPU enablement for PURE under WSL2 (Ubuntu 20.04), RTX 3080.

## Findings (from final probe)
- Inside `pytorch/pytorch:2.1.2-cuda11.8-cudnn8-runtime`, `LD_PRELOAD=/usr/lib/wsl/lib/libcuda.so` succeeds (`dlopen` OK), and `/dev/dxg` is present.
- `torch.version.cuda` reports 11.8, but `torch.cuda.is_available()` remains **False** with `cudaGetDeviceCount Error 500`.
- Torch’s CUDA shared objects are not linking to a compatible driver interface under this Docker-on-WSL stack (likely symbol/version/layout mismatch).
- Podman v3.4.2 cannot be wired to NVIDIA Toolkit in this WSL20.04 environment (legacy hook exits, nvidia-ctk lacks podman runtime support).

## Decision Needed (Architect)
1. **Stack-aligned primary path:** Upgrade WSL distro to **Ubuntu 22.04** and deploy **Podman v4+** with **NVIDIA Container Toolkit** (OCI hooks). Then re-run GPU smokes and mini PURE check.
2. **Interim demo path (temporary exception):** Upgrade Docker Desktop to a version with fully working WSL GPU runtime for PT 2.1.x, and allow short, cache-friendly PURE runs via Docker only, while we schedule the Podman v4 migration.

**GO-gate preserved:** No long runs without explicit user approval.

— Implementation Agent 7N
