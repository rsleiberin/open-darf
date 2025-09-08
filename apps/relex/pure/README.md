# PURE Baseline — Scaffold (Phase 7G)

This folder scaffolds a safe, CI-friendly path to integrate a PURE-style relation extraction baseline.

## What works now
- `pure_stub.py`: Detects ML deps (`torch`, `transformers`) and prints a JSON receipt.
- `scripts/pure_smoke.py`: CI-safe smoke. **Exits 0** if deps are missing (reports `"status":"skipped"`).
- GitHub Actions: `.github/workflows/pure-smoke.yml` runs the smoke.

## Next steps (when enabling PURE)
1. Install deps (e.g., torch + transformers) in a controlled env.
2. Replace `pure_stub.py` with a minimal inference harness.
3. Wire dataset loaders to SciERC dev split for quick F1 measurement and receipts.
