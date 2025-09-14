# Phase 7S · Group 2 — Native Ubuntu Validation Gate

**Status:** BLOCKED on WSL2; proceed on *native* Ubuntu 22.04 + RTX 30/40 (≥8GB VRAM).

## Required Steps (once on native Ubuntu)
1) Run `./install.sh`
2) Run `./validate/run_minimal.sh`
3) Run `./validate/generate_evidence.sh`
4) Verify:
   - `torch.cuda.is_available() == True`
   - Evidence tarball `open-darf-report-<HOST>-<TS>.tar.gz` created

## Acceptance Checks
- Ubuntu 22.04 LTS
- NVIDIA driver compatible with CUDA
- `nvidia-smi` shows GPU
- Timing precision: sub-ms

(Generated automatically to persist gate requirements.)
