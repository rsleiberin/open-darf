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

## Parser flags

- `PIPELINE_PARSER_HTML=1` — enable minimal HTML parser (UTF-8/Latin-1 decode).
- `PIPELINE_PARSER_PDF=1` — enable PDF detector stub (no text extraction).
- `PIPELINE_PARSER_DOCX=1` — enable DOCX detector stub (no unzip/parse).
- `PIPELINE_FORCE_MIME=1` — bypass text/plain fast-path and route via flags.
