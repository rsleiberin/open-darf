# Stream 1 — Constitutional Constraint Engine (Phase 1)
- Package: `apps/constitution_engine`
- Target: p95 < 170ms for `validate()`
- Optional Neo4j lookup; degrades gracefully if unavailable
- Bench: `python -m scripts.bench_constitution_engine` → writes `docs/audit/stream1/<ts>/validation.json`
