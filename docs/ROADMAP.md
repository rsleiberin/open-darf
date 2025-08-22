# DARF Document Processing and Knowledge Graph Roadmap

**Last updated:** 2025-08-22 (research-aligned)

---

## Executive Overview

DARF’s near-term goal is to stand up a **document processing → provenance anchoring → bias filtration → entity/relationship extraction → HyperGraphRAG** pipeline that is **provably aligned** (constitutional constraints), **observable** (receipts + metrics), and **performant** (p95 < 50 ms for hot paths) while preserving **sovereignty** and **revocation** guarantees.

This roadmap translates research artifacts into concrete, incremental deliverables with receipts and CI policy gates.

---

## Phasing at a Glance

- **Phase 1 – Ingestion Foundations (current)**
  - Deterministic **SHA-256 anchoring** (doc + paragraph sub-anchors)
  - **Provenance graph (PROV-O)** initialization (Entity/Activity/Agent)
  - **Routing** (Lambda vs EC2) + MinIO contract (mocked in tests)
  - Unit tests, perf smoke, receipts & metrics stubs

- **Phase 2 – Constitutional Engine & API hardening** ✅ (shipped)
  - Tri-state evaluation (ALLOW/DENY/ABSTAIN) with precedence & scopes
  - `/validate` FastAPI route; **reason codes**; **receipts** (JSONL)
  - Metrics scaffold; optional index dry-run utilities

- **Phase 3 – Bias Filtration + Extraction**
  - Bias detection via **CBDT** (Contextualized Bi-Directional Dual Transformer) for technical/academic corpora
  - Lightweight NER + relationship extraction; language-agnostic where feasible

- **Phase 4 – HybridRAG / HyperGraphRAG**
  - Hierarchical chunking + vector + graph retrieval orchestration
  - Constitutional validation integrated into retrieval and synthesis steps

- **Phase 5 – Observability & SLO tightening**
  - p95 latencies, compression targets, receipt coverage, and live dashboards
  - Rotating receipts with correlation IDs and latency fields

---

## Targets (from research)

- **Compression:** ≥ 47× semantic/contextual compression with hierarchical chunking
- **Latency:** sub-50 ms p95 graph reads on hot paths; ≤ 170 ms constitutional validation p95
- **Recall:** ≥ 60 % improvement in relevant context recall with HyperGraphRAG
- **Bias detection:** ≥ 91 % F1 on technical/academic domains (CBDT)

---

## Architecture Primitives

- **Storage**
  - **MinIO** for artifacts (originals, normalized docs)
  - **PostgreSQL** for anchors & operational metadata
  - **Neo4j** for provenance + knowledge graph
  - **Qdrant** for vector search
  - **Redis** for cache/coordination

- **Compute**
  - **Lambda** for small doc transforms; **EC2** for large workloads
  - Background workers via **Dramatiq**; broker **RabbitMQ**

- **Observability**
  - JSONL receipts (append-only), metrics (Prometheus/Otel), correlation IDs

- **Governance**
  - Constitutional validation engine on all sensitive ops
  - Receipts-backed auditability and revocation pathways

---

## Phase 1 – Scope & Deliverables (repo work underway)

**Goal:** Make ingestion deterministic and testable without live services.

**Deliverables**
1. **Anchoring**
   - `apps/document_processor/anchoring.py`
     - `create_anchor_hierarchy(doc)` → base + paragraph anchors (`sha256:<hash>:<type>:<ts>:para_<i>:<span>:<sha>`)

2. **Routing**
   - `apps/document_processor/routing.py`
     - `decide_processor(size_mb)` with `MAX_DOCUMENT_SIZE_LAMBDA_MB` env threshold

3. **Provenance (PROV-O)**
   - `apps/provenance/prov_logging.py`
     - Pure Cypher generator for `Entity/Activity/Agent` ingestion events

4. **Tests & Perf**
   - `tests/unit/*` (anchoring, routing, provenance)
   - `tests/performance/test_perf_smoke.py` (fast placeholder)

5. **Docs**
   - This `docs/ROADMAP.md` (canonical)
   - Pointers under `docs/architecture/TECHNICAL_DECISIONS.md`, `docs/implementation/PROVENANCE_GUIDE.md`

6. **CI**
   - `performance-testing.yml` (PR + nightly)

**Exit criteria**
- Unit + perf smoke green in CI
- Anchors deterministic; provenance Cypher valid; receipts baseline retained

---

## Phase 2 – Summary (completed)

- Tri-state constitutional engine & `/validate` route
- Centralized reason codes
- JSONL receipts (env-resolved path per emit; thread-safe)
- Metrics counters/labels scaffold
- Optional index dry-run utility
- CI stabilized via `tests/conftest.py` for imports

---

## Phase 3 – Bias Filtration + Extraction

**Objectives**
- Integrate **CBDT** for bias detection on technical/academic docs
- NER + simple relation extraction; produce typed nodes/edges
- Emit **bias analysis receipts** with model versions and thresholds

**Tasks**
- Model serving stub (CPU-first, GPU-optional)
- Batch evaluation suite and golden datasets
- Policy: fail-closed on high-risk bias score unless explicitly overridden

**SLOs**
- Bias pass pipeline adds ≤ 35 ms p95 for short docs; batch path out-of-band

---

## Phase 4 – HybridRAG / HyperGraphRAG

**Objectives**
- Hierarchical chunking → vector + graph retrieval → constitutional-checked synthesis
- Query planner that selects between dense, sparse, and graph traversals

**Tasks**
- Chunker with overlap rules, language-aware boundaries
- Retrieval orchestrator (LangChain/Autogen guardrails optional)
- Neo4j + Qdrant hybrid queries; provenance propagation

**SLOs**
- End-to-end retrieval p95 ≤ 120 ms (hot cache), ≤ 250 ms (cold)

---

## Phase 5 – Observability & SLO Tightening

**Objectives**
- Live dashboards for latency, receipts volume, bias outcomes
- Correlate receipts with decision paths and reason codes

**Tasks**
- Prometheus metrics export + Grafana boards
- Receipt rotation & enrichment (policy_id, latency_ms, corr_id)
- Perf regression guards (CI gates on p95 deltas)

---

## Data Contracts & Schemas (initial)

- **Anchor record (PostgreSQL)**
  - `anchor_id`, `doc_id`, `doc_type`, `sha256`, `ts`, `para_spans[]`

- **Provenance (Neo4j)**
  - `(doc:Entity:Document {id, type})`
  - `(act:Activity {id, type, startTime})`
  - `(ag:Agent {id, type})`
  - Relationships: `:wasGeneratedBy`, `:wasAssociatedWith`

- **Vector index (Qdrant)**
  - `collection: "darf_docs_v1"`; payload: `anchor_id`, `doc_id`, `section_path`

---

## Receipts & Metrics (expanded plan)

- **Receipt fields** (minimum): `decision`, `reason_code`, `principal_id`, `correlation_id`, `latency_ms`, `policy_id`, `ts`
- **Metrics**: counters (`decision_total{decision,reason_code}`), histograms (`latency_ms_bucket`)

---

## Risks & Mitigations

- **Model drift** → pin versions; periodic evals; receipt lineage
- **Graph latency spikes** → bounded traversals; hot path indices; cache keys in Redis
- **Cost pressure** → Lambda threshold tuning; batch large docs on EC2; compression

---

## Policy Gates (per PR)

- Exactly one of each: `type:*`, `status:*`, `priority:*`
- ≥ 1 `area:*`
- Append-only receipts & audit artifacts for perf-sensitive changes
- No `.tla/.cfg` changes in status-only PRs

---

## Definition of Done (phase-scoped)

- Tests & CI green; p95 targets met or receipts added
- Docs updated (this file + pointers)
- Audit receipts under `docs/audit/<stream>/<timestamp>/…` where relevant

---

## Next Up (shortlist)

- Wire MinIO upload client + content-type normalization
- Neo4j driver integration for provenance writes
- Bias filtration service stub + golden set
- Chunker + dual-indexer (Qdrant + Neo4j)
- Perf dashboards with p95/p99 tracking

---

## Appendix – Why this works

- **Determinism first** (anchors, receipts) → reliable regression & audits
- **Separation of concerns** → swap components without breaking contracts
- **Hybrid retrieval** → higher recall with tractable latency
- **Constitutional guard** → safety and sovereignty by construction

This roadmap is maintained as the **single source of truth** for implementation sequencing. Keep it tight; append receipts where claims affect SLOs or safety.
