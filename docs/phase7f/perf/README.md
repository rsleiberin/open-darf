# Phase 7F — Performance Plans (C12/C13)

- **C12 Neo4j runtime tuning**: docs-only plan (heap/page cache/GC). Actual apply occurs in infra; here we persist the plan and verify propagation p95 < 100ms via receipts.
- **C13 Qdrant HNSW/quantization sweep**: docs-only simulated sweep over {m, ef_construct, ef_search} targeting p95 ≤ 7.745ms; persist best config & grid.

Receipts live under:
- `var/receipts/phase7f/neo4j_tuning/*/summary.json`
- `var/receipts/phase7f/qdrant_perf/*/summary.json`
