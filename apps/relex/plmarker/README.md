# PL-Marker Path (Phase 7G)

This scaffold provides:
- `runner.py` — deps-aware stub that emits a receipt; real PL-Marker inference TBD.
- `scripts/plmarker_bridge_run.sh` — bridge wrapper to import best heuristic metrics into PL-Marker receipts (schema-compliant).
- `.github/workflows/plmarker-optin.yml` — label-gated CI (`ci:run-plmarker`) to run wrapper, validate receipts, and upload artifacts.

When enabling real PL-Marker:
1) Implement inference/eval in `runner.py` (reuse SciERC adapter).
2) Ensure `metrics.json` matches `docs/schemas/metrics_v1.json`.
3) CI remains the same; artifacts will reflect true PL-Marker runs.
