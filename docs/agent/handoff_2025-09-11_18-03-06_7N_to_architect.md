# Handoff — Implementation Agent 7N → Architect
**When:** 2025-09-11  
**Context:** Phase 7N — GPU Infrastructure Activation (WSL2 Ubuntu 20.04, RTX 3080, Windows driver 566.24)

## TL;DR
- **Working:** GPU visible in containers via `nvidia-smi`.
- **Blocked:** `torch.cuda.is_available()` remains **False** inside PyTorch CUDA images (12.1 and 11.8) despite `/dev/dxg` and `/usr/lib/wsl/lib` bind; repeated `cudaGetDeviceCount() Error 500`.
- **Root cause hypothesis:** Torch CUDA user-space ↔ WSL `libcuda.so` symbol/layout mismatch under **Docker-on-WSL**; Podman is **3.4.2** here and cannot be wired to NVIDIA Toolkit reliably.
- **Action requested:** Choose a runtime path.

## Pivot Options (Request Decision)
1. **Primary (stack-aligned):** Upgrade WSL distro → **Ubuntu 22.04**, install **Podman v4+** via libcontainers stable, configure **NVIDIA Container Toolkit** → rerun smokes + mini PURE.
2. **Interim (timeboxed):** Upgrade Docker Desktop GPU stack and allow **short, cache-friendly PURE runs** in Docker while we schedule Podman v4 migration.

## What we did this session
- Purged deprecated **ProjectAtomic PPA**; restored clean APT.
- Verified GPU in-container via **CUDA base** (`nvidia-smi` ✔).
- Attempted Torch CUDA with multiple images (PT 2.1.2 **cu12.1** and **cu11.8**), with:
  - `--gpus all`, `--device /dev/dxg`, `-v /usr/lib/wsl/lib`.
  - `LD_LIBRARY_PATH` and `LD_PRELOAD=/usr/lib/wsl/lib/libcuda.so`.
- Captured diagnostics, decisions, and explicit **GO-gate** adherence.

## Artifacts
- Decisions:
  - `docs/decisions/2025-09-11_podman_gpu_blocker.md`
  - `docs/decisions/2025-09-11_runtime_blocker_addendum.md`
  - `docs/decisions/2025-09-11_runtime_blocker_seal.md`
- Audit:
  - `docs/audit/runtime_snapshot.txt` (earlier)
  - `docs/audit/final_runtime_snapshot_*.txt`
  - `docs/audit/nvidia_smi_*.txt`

## Next Minimal Steps After Decision
- If **Podman v4 path**: upgrade WSL distro to 22.04, `podman 4.x`, `nvidia-container-toolkit`, run short Podman smokes (`nvidia-smi`, Torch tiny op), then mini PURE quickcheck.
- If **Docker interim**: upgrade Docker Desktop, rerun Torch CUDA probe; if green, run mini PURE quickcheck (short), then seek **GO** for full PURE.

— Implementation Agent 7N
