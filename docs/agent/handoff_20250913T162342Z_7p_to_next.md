# Handoff — Phase 7P → Next Implementation Agent

**Timestamp (UTC):** 20250913T162342Z  
**Agent:** 7p (Implementation)  
**Repo:** This repo was treated as working tree for docs/agent + docs/audit updates.

---

## 1) Current Status (Single-Provider libcuda ✅ / Torch CUDA ❌)

- **GPU/Driver (host):** GeForce RTX 3080, driver 566.24, driver CUDA 12.7 (WSL2).
- **WSL dual-lib issue:** Reproduced inside containers; **resolved in CUDA base** by enforcing the **real** `/usr/lib/wsl/drivers/.../libcuda.so.1.1` via `LD_PRELOAD` and a shim that places it first.  
  - **Proof:** `LD_DEBUG=libs` shows exactly **one** `calling init:` line for `/mnt/realnv/libcuda.so.1.1`.
- **nvidia-smi in containers:** Works reliably with `--gpus all` (CUDA 12.1.1 runtime image).
- **PyTorch (cu121) in container:** `torch.cuda.is_available()` remains **False** with **Error 500: named symbol not found**, even when:
  - Single-provider `libcuda` is enforced.
  - WSL shim libs (`libdxcore`, `libd3d12`) are present when required.
  - `ctypes.cuInit(0)` **succeeds** and device count=1, but Torch still reports `is_available: False`.

**Bottom line:** Driver init path is clean, but **Torch runtime + WSL DX interop** still fails availability.

---

## 2) Root-Cause Analysis (RCA) — What we know

- **No multi-provider collision** in CUDA base after the shim; the earlier two-init condition is gone.
- Torch error persists even when `ctypes` probes succeed and symbols like `cuGetProcAddress` are present on `libcuda`.
- Torch images lack `libcudart.so.12` (not needed for driver API, but sometimes referenced by code paths); adding cudart explicitly did not restore availability and caused a segfault in one probe (likely ABI/library mismatch when mixing pieces from different distros).
- **Hypothesis (to validate):** Torch’s CUDA checks under WSL require consistent pairing of:
  1) Real `libcuda` from the WSL driver,
  2) Correct **NVML** exposure (`libnvidia-ml.so.1`) and
  3) The **WSL DX** shims **from inside** the container base image variant that is known-good with the NVIDIA toolkit.  
  Mixing Torch runtime image (which includes its own stack decisions) with manual binds may leave a subtle unresolved dependency.

---

## 3) Green Path Recommendation

**Use NVIDIA CUDA 12.1.1 runtime as the base** and install Torch cu121 wheels there (we tested this flow already, but availability was still False under our manual shims). Next agent should:

1. **Switch to official CUDA + NVIDIA Container Toolkit path only** (no manual LD_PRELOAD):
   - Ensure `nvidia-ctk` is healthy on host (we earlier saw symbol errors when using Podman; Docker Desktop now in use):
     - `nvidia-ctk runtime configure --test` should PASS.
     - Confirm `/usr/local/nvidia/lib64` is mounted in the container (it was missing in some runs).
2. **If `/usr/local/nvidia/lib64` is missing**, reinstall/repair NVIDIA Container Toolkit on Docker Desktop WSL distro:
   - `sudo apt-get install -y nvidia-container-toolkit`
   - `sudo nvidia-ctk runtime configure --runtime=docker`
   - `sudo service docker restart` (or restart Docker Desktop)
   - Re-run CUDA base `nvidia-smi` **and** verify **that** `/usr/local/nvidia/lib64` exists inside the container.  
3. **Retest Torch cu121** without manual `LD_PRELOAD` (pure runtime injection).  
   - If still failing, test a **known-good NVIDIA PyTorch container** (NGC) that aligns CUDA/driver expectations.

*Rationale:* This avoids subtle ABI mismatches from stitching cudart/dxcore pieces by hand.

---

## 4) What’s already captured

- **Receipts file:** `docs/audit/phase7p_receipt_20250913T162342Z.log`  
  Includes host `nvidia-smi`, real driver dir listing, Docker runtime excerpt, CUDA base `nvidia-smi`, single-provider init proof, and Torch availability probe output.

- **Key invariant verified:** Single-provider libcuda init inside container.

---

## 5) Next Steps (Checklist for the next agent)

- [ ] Repair NVIDIA Container Toolkit so container sees `/usr/local/nvidia/lib64` by default.
- [ ] Re-run `CUDA 12.1.1` base with `--gpus all` and confirm lib paths present **without** LD overrides.
- [ ] Install Torch cu121 in that base and confirm `torch.cuda.is_available()==True`, allocate CUDA tensor.
- [ ] If False: compare `ldd $(python -c "import torch,os,inspect; print(os.path.dirname(inspect.getfile(torch)))")/lib/*.so` for missing deps; check `libnvidia-ml.so.1` and PTX JIT compiler presence/versions.
- [ ] Optionally validate with an **NGC PyTorch** image to isolate Torch build/runtime coupling issues.

---

## 6) Branch, Tag, and Files

- **Branch:** `phase7p/wsl-cuda-torch-rca`
- **Tag:** `phase7p_checkpoint_20250913T162342Z`
- **Docs:**
  - `docs/agent/handoff_20250913T162342Z_7p_to_next.md` (this file)
  - `docs/audit/phase7p_receipt_20250913T162342Z.log`

---

## 7) Deviations & Notes

- Avoided destructive Docker pruning; all `docker run` used `--rm`.
- Did not persist LD overrides globally; all scoped to container runs.
- No edits to TLA-owned files (`.tla/.cfg`).

