# Open-DARF — Collaborator Invite (Phase 7S)

Thank you for helping validate our minimal Open-DARF flow.

## What you'll do (native Ubuntu 22.04 + RTX 30/40 recommended)
1. Unpack the provided **open-darf_minimal_*.tar.gz**.
2. In the `open-darf/` folder:
   - Run: `./install.sh`
   - Run: `./validate/run_minimal.sh`
   - Run: `./validate/generate_evidence.sh`
3. Send back:
   - The generated `open-darf-report-<HOST>-<TS>.tar.gz`
   - (Optional) Any JSON receipt produced by `scripts/oneclick.sh`
4. If anything fails, please include console output and `docs/phase7s/TROUBLESHOOTING.md`.

## Requirements
- Ubuntu **22.04 LTS** on bare metal (not WSL)
- NVIDIA RTX **30/40** series GPU (≥8GB VRAM)
- Recent NVIDIA driver compatible with CUDA

## Optional: One-command path
- From `open-darf/`, run: `make oneclick`
  - This creates a JSON receipt in `var/receipts/open-darf/`.

Thank you!
