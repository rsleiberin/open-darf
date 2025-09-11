# Decision Record — Podman v3.4.2 GPU Enablement Blocker (WSL2, Ubuntu 20.04)

**When:** 2025-09-11  
**Context:** Phase 7N — GPU Infrastructure Activation (PURE on GPU, gaming-safe).  
**Machine:** WSL2 Ubuntu 20.04, RTX 3080, Windows driver 566.24.  

## Current State
- Docker + NCT: `nvidia-smi` OK in CUDA base; PyTorch control image can initialize CUDA.
- PURE image: PyTorch fails `cudaGetDeviceCount()` Error 500 due to driver libs not injected/mis-ordered.
- Podman: version pinned at **3.4.2** on Ubuntu 20.04. NVIDIA OCI runtime integration via `nvidia-ctk` **not supported** (`unrecognized runtime 'podman'`). Legacy hook `nvidia-container-runtime-hook` exits 1.

## Blocker
- **Tech stack requires Podman**, but **v3.4.2** cannot be cleanly wired with NVIDIA Toolkit on this host. Driver libs aren’t injected into containers, so CUDA remains invisible to Torch under Podman.

## Options (Requesting Architect Direction)
1. **Upgrade WSL distro to Ubuntu 22.04** (or newer) → Install **Podman v4+** (libcontainers stable) → Configure **NVIDIA Container Toolkit** for Podman → Re-run smokes and PURE.
2. **Temporary exception:** Allow **Docker** for PURE runs while we schedule the WSL/Podman upgrade. We will:
   - Keep runs short and cache-friendly (respecting GO-gate).
   - Avoid committing Docker-specific configs to `darf-source`.
   - Continue pursuing Podman v4 path in parallel.

**Recommendation:** Approve temporary Docker exception for PURE to unblock demo while planning a fast WSL22.04 + Podman v4 migration.

## Acceptance Impact
- **Short-term:** We can complete GPU smoke + mini inference under Docker today (with cache mounts).
- **Medium-term:** Podman v4 migration required to align with stack and reproducibility goals before the grant deadline.

— Implementation Agent 7N
