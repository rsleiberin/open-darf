# Handoff — 7N → Next Implementation Agent

## Current State
- GPU visible to containers (`nvidia-smi` OK).
- Torch CUDA fails in PyTorch images on WSL (Error 500 on `cudaGetDeviceCount`), even with `/dev/dxg` + `/usr/lib/wsl/lib` bind and `LD_PRELOAD`.
- Podman is **3.4.2** → NVIDIA Toolkit automation unsupported; legacy hooks error.

## Do-First (after architect decision)
- **If Podman v4 approved:**
  1) Upgrade WSL distro to **Ubuntu 22.04**.  
  2) `apt-get install -y podman crun fuse-overlayfs slirp4netns uidmap` (via libcontainers stable).  
  3) `apt-get install -y nvidia-container-toolkit && sudo nvidia-ctk runtime configure --runtime=podman`.  
  4) Ensure `[engine].hooks_dir` includes `/usr/share/containers/oci/hooks.d`.  
  5) **Smokes (short):**  
     - `podman run --rm nvidia/cuda:12.1.1-base-ubuntu20.04 nvidia-smi`  
     - `podman run --rm pytorch/pytorch:2.1.2-cuda11.8-cudnn8-runtime python -c "import torch; print(torch.cuda.is_available())"`
- **If Docker interim approved (timeboxed):**
  1) Upgrade Docker Desktop to latest stable.  
  2) Re-run Torch CUDA probe in PT 2.1.2 **cu11.8**.  
  3) If green, run **mini PURE** quickcheck (Torch-only) and, upon explicit **GO**, the full PURE run with cache mounts.

## Guardrails
- Respect **GO-gate**.  
- Keep runs short; mount caches to avoid re-downloads.  
- Document any deviations in `docs/decisions/`.

## Useful Paths
- Decisions: `docs/decisions/`  
- Audit logs: `docs/audit/`  
- Quickcheck: `external/PURE/code/quickcheck.py`
