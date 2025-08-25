# Phase-3 — Document Processing Pipeline (Scaffold)

This PR introduces a **passing scaffold** for the pipeline:
- `apps/pipeline/ingest|parse|process|receipts` with import-only stubs
- Tests under `tests/pipeline` (sanity + contracts)
- CI job `Phase-3 Pipeline (scaffold)` running only `tests/pipeline`

## Next Increments
1) Wire MinIO ingest to existing adapter (no live service in CI).
2) Real parsers (PDF/DOCX/HTML) behind feature flags or mocked in CI.
3) CBDT bias checks integrated; write receipts under `docs/audit/pipeline/...`.
4) Perf receipts for p95 timings; obs counters (allow/deny/indet when applicable).

## Perf/Obs (flag-gated)

Set `PIPELINE_PERF=1` to include timing stats in receipts:
- `perf.parse_ms` and `perf.process_ms` with `p50/p95/max/avg/n`
- `obs.parser_counts` (e.g., `{"text": N, "noop": M}`)
