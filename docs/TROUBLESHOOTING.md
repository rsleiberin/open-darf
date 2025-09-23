# Troubleshooting (Open-DARF Minimal)

## GPU validation blocked on WSL
- Symptom: `is_wsl: 1` in receipts; CUDA tests skipped or fail.
- Action: Use **native Ubuntu 22.04** on a machine with RTX 30/40 (≥8GB VRAM).

## Missing `nvidia-smi`
- Install NVIDIA drivers compatible with your GPU and CUDA.
- Re-run `bin/doctor.sh` to confirm.

## Python missing
- Install `python3` from system packages; re-run `./install.sh`.

Receipts are written to `var/receipts/open-darf/…json` for machine processing.
