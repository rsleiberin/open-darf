# Phase 3 — Flags, Receipts, and Debug Cookbook

## Flag Matrix (defaults are OFF for PR CI)
- `PIPELINE_PERF` — include timing + write receipts.
- `PIPELINE_CBDT` — run CBDT pass; provider via `PIPELINE_CBDT_PROVIDER` (default: `null`, use `local` in tests).
- `PIPELINE_ANCHORS` — emit SHA-256 anchors; add `PIPELINE_ANCHORS_SUB` for sentence sub-anchors.
- `PIPELINE_PROV` — include compact PROV-O JSON-LD bundle.
- `PIPELINE_OSCAR` — run OSCaR stub (risk_score + tags).
- Budgets: `PIPELINE_CBDT_P95_BUDGET_MS`, `PIPELINE_ANCHOR_P95_BUDGET_MS`.

## Receipts (append-only)
- Pipeline runs: `docs/audit/pipeline/pipeline_e2e/<stamp>/run_once.json`
- CBDT: `docs/audit/pipeline/pipeline_cbdt/<stamp>/<doc>.json` and `_last/<doc>.json`
- Anchors: included in run receipts; no PII (sub-anchors omit raw text)
- PROV: `docs/audit/pipeline/pipeline_prov/<stamp>/<doc>.json` and `_last/…`
- OSCaR: `docs/audit/pipeline/pipeline_oscar/<stamp>/<doc>.json` and `_last/…`
- Perf (scope microbench): `docs/audit/perf/scope/<stamp>/bench.json`

## Debug Cookbook
1. **Nothing happening?** Verify flags are set (export the ones above). Add `PIPELINE_PERF=1` to see receipts.
2. **Obs counters silent?** Ensure no `OBS_FAIL_ON_EMIT`; call `from apps import obs; print(obs.snapshot())`.
3. **Receipts missing?** Check `_last/` mirrors; EOF fixes may run via pre-commit.
4. **Budget failures?** Override budget env locally; investigate per-pass `timing_ms` in receipts.
5. **Runner wiring sanity:** `tests/pipeline/test_runner_*` show minimal MemSource patterns.

*All new features are env-gated; production posture stays fail-closed.*
