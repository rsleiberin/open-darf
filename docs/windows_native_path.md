# Windows → Native Ubuntu Path (Phase 7R Tier-1)

**Goal:** Run Open-Darf validator on *native* Ubuntu with NVIDIA driver + CUDA so `torch.cuda.is_available() == True`.

## Option A — Dual-boot Ubuntu 22.04 LTS (recommended)
1. **Prep USB:** Use Rufus on Windows to write the Ubuntu 22.04 LTS ISO to a ≥8 GB USB stick.
2. **Backup:** Back up important Windows data.
3. **BIOS/UEFI:**
   - Enable **AHCI** for SATA (if applicable).
   - Keep **Secure Boot** ON if you prefer (you will need to enroll NVIDIA’s DKMS via MOK on first driver load), or OFF for a smoother driver path.
4. **Shrink Windows partition:** In Windows Disk Management, shrink to leave free space (≥ 100 GB preferred).
5. **Install Ubuntu:** Boot the USB, choose “Install Ubuntu alongside Windows”. Create a user, let installer create partitions.
6. **First boot:** `sudo apt update && sudo apt install -y ubuntu-drivers-common`
7. **Install NVIDIA driver:** `sudo ubuntu-drivers autoinstall` → **reboot**.
8. **Verify GPU:** `nvidia-smi` shows your GPU and driver version (R535+/R550+).
9. **Clone & run:** `git clone <your repo>` → `cd darf-source` → `./install.sh`

## Option B — Dedicated drive (clean install)
Same as Option A, but install Ubuntu onto a separate SSD/NVMe. This keeps Windows disk untouched.

## Option C — VM with GPU passthrough (advanced)
- Requires a hypervisor and hardware/firmware support (IOMMU/VT-d), proper GPU isolation, and host driver configuration.
- If passthrough succeeds, `/dev/nvidia*` will exist inside the guest and `nvidia-smi` will match bare-metal.

## Notes & Troubleshooting
- **Secure Boot (MOK):** If Secure Boot is enabled, Ubuntu will prompt MOK enrollment so the NVIDIA kernel module can load. Follow the on-screen steps after reboot.
- **Driver mismatch:** If autoinstall fails, pick a known-good meta-package, e.g. `sudo apt install -y nvidia-driver-535`.
- **Verify CUDA userspace:** `ldconfig -p | grep -E 'libcuda|libcudart'` should list libraries from `/usr/lib/x86_64-linux-gnu` or similar (not `/usr/lib/wsl`).
- **Torch CUDA:** Our installer uses official cu12x wheels: `--index-url https://download.pytorch.org/whl/cu126`

## What success looks like
- `nvidia-smi` → shows GPU + driver.
- Python: `import torch; torch.cuda.is_available()` → **True**.
- `./install.sh` completes all stages and produces `open-darf-report-<host>-<ts>.tar.gz`.
