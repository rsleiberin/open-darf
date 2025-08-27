# Phase 5 — Implementation Notes

## Feature flags (safe defaults)
- `EXTRACTOR_SCI=0` · `EXTRACTOR_BIO=0` · `EXTRACTOR_TEXT2NKG=0` · `TEMPORAL_GRAPH_MODEL=0`
- Perf: `RUN_PERF=0` by default (enable locally only)

## Components
- **Guards:** `apps/guards/constitutional.py` (tri-state), `apps/guards/middleware.py` (pre/post wraps)
- **Extractors:** `apps/extractors/{scibert_extractor,biobert_extractor,text2nkg_extractor}.py`
- **Temporal:** `apps/knowledge_graph/temporal_model.py`
- **Orchestrator:** `apps/knowledge_graph/entity_extraction.py` (entities · relations · temporals)
- **Hypergraph:** `apps/knowledge_graph/hypergraph.py`
- **Perf:** `tools/perf/run_perf.py`, tests in `tests/performance/`

## Testing
- Unit: `pytest -q tests/extractors tests/guards tests/knowledge_graph`
- Perf (opt-in): `RUN_PERF=1 pytest -q tests/performance`

## Receipts & audits
- Receipts live under `var/receipts/**`.
- Mirror to `docs/audit/phase5/` when promoting results.

## Rollback & safety
- All ML paths flag-gated; middleware enforces DENY precedence and fail-closed semantics.
- Set flags back to `0` to disable; orchestrator returns INDETERMINATE with empty payloads.
