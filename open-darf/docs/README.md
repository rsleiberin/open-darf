# Open-DARF (Minimal Extract)

A simplified, grant-evidence oriented snapshot.

## Commands
- `make quickstart` — installer → minimal validate → evidence tarball
- `make oneclick`  — same as above, plus a **JSON receipt** in `var/receipts/open-darf/`

## Files
- `install.sh` — minimal installer with environment gate hints
- `validate/run_minimal.sh` — quick pipeline probe (placeholder if full pipeline absent)
- `validate/generate_evidence.sh` — bundles a system/evidence tarball
- `scripts/quickstart.sh` — orchestration for quickstart
- `scripts/oneclick.sh` — orchestration + JSON receipt
- `bin/doctor.sh` — environment probe
- `docs/TROUBLESHOOTING.md` — common issues

> GPU validation requires **native Ubuntu 22.04 + RTX 30/40 (≥8GB VRAM)**.
