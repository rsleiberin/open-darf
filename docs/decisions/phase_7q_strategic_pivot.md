# Phase 7Q Strategic Response: WSL2 Limitation Recognition

**Decision:** Pivot GPU validation from WSL2 containers to native Linux (Ubuntu 22.04+).

**Evidence summary:**
- `nvidia-smi` and DXG path visible in containers across CUDA 12.1 / 12.6.2.
- `ctypes` loads `libcuda.so.1` and (after install) `libcudart.so.12`.
- PyTorch fails at `cudaGetDeviceCount` with Error 500 (“named symbol not found”) across cu121 and cu126 wheels.
- WSL single-provider `libcuda` enforcement and DX12/ML support libraries mounted; still failing.

**Risk/Impact:**
- Continued WSL2 debugging is high-risk against the Oct 1, 2025 deadline.
- Native Linux path has high probability of immediate success; preserves time for demo.

**Actions authorized in 7Q:**
- Maintain receipts for reproducibility.
- Prepare native Linux validator path and test matrix mirroring 7Q probes.
- Keep WSL2 path documented as “non-blocking, not on critical path”.

**Validation plan (native):**
- Ubuntu 22.04 LTS, NVIDIA drivers (535+ or latest stable), Docker + nvidia-container-toolkit.
- PyTorch cu12x wheels in `nvidia/cuda:12.6.x-runtime-ubuntu22.04` with `--gpus all`.
- Accept only `torch.cuda.is_available() == True` with `device_name` readout.
