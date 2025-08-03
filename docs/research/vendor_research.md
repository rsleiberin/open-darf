# Vendor Research & Decisions  
_Last updated: 2025-08-03_

## Contents
1. Locked-In Components  
2. Pending / Open Slots  
3. Decision Log Conventions  

---

## 1  Locked-In Components

> For every slot we record **Purpose & Role**, **Why It Was Chosen**, and **Alternatives Considered**.  
> The goal is to surface the rationale so future contributors know _why_ a component is here and what was rejected.

### 1.1  PostgreSQL 15 (+ SQLAlchemy / Alembic)

**Purpose & Role** – canonical relational store for agent configs, audit logs and any data that demands ACID guarantees.  
**Why chosen** – battle-tested, rich JSONB & extension ecosystem, runs on anything from a Pi to a cluster, excellent async Python tooling.  
**Alternatives** – MySQL/MariaDB, SQLite, NewSQL; each dropped due to weaker JSON support, scaling limits or unnecessary complexity for now.

---

### 1.2  Neo4j 5 (Community)

**Purpose & Role** – long-term semantic memory / knowledge-graph backing complex multi-hop queries.  
**Why chosen** – native graph engine, expressive Cypher, strong single-node performance, active ecosystem.  
**Alternatives** – JanusGraph (over-engineered for single-node), ArangoDB (multi-model trade-offs), TigerGraph/Dgraph/Memgraph (licensing or maturity issues).

---

### 1.3  Qdrant v1

**Purpose & Role** – high-performance vector index for semantic similarity search inside the RAG loop.  
**Why chosen** – Rust core ⇒ low footprint; embedded/offline mode aligns with off-grid goal; payload filters and GPU path ready.  
**Alternatives** – Weaviate (heavier), Milvus (multi-service), pgvector (convenient but slower at scale) – see architecture brief section “Vector Database – Qdrant”.

---

### 1.4  RabbitMQ 3

Message backbone for durable task queues; praised for back-pressure handling and small ARM-friendly footprint.  
Alternatives (Redis Streams, Kafka, NATS, ZeroMQ) were ruled out for either weaker durability semantics or excessive resource overhead.

---

### 1.5  Dramatiq + Redis 7

- **Dramatiq** orchestrates async tasks/workflows; chosen over Celery for a cleaner API and native async support.  
- **Redis** backs Dramatiq results & rate-limiting, and serves as the low-latency cache / pub-sub bus.  
  *Why not Celery + Memcached?* Complexity and feature overlap respectively.

---

### 1.6  MinIO

Self-hosted S3-compatible object store for raw documents, datasets, model artefacts; single-binary elegance and erasure-coding support beat Ceph’s operational weight.

---

### 1.7  LangChain + AutoGen + GraphRAG

Software—not services—but captured here because they anchor how agents interact with every datastore, enabling hybrid vector + graph retrieval and multi-agent workflows.

---

## 2  Pending / Open Slots

| Slot | Why Needed | Leading Candidates |
|------|------------|--------------------|
| **Document Store** | Raw HTML / JSON staging before indexing; replication friendliness | CouchDB (offline sync), MongoDB CE, LiteFS + SQLite |
| **Time-Series DB** | Future IoT / metrics ingestion | TimescaleDB (PG extension), InfluxDB, VictoriaMetrics |
| **Secrets / Config** | Remove creds from env files | HashiCorp Vault, SOPS, Doppler |
| **Observability Stack** | Unified metrics & tracing | Prometheus + Grafana, OpenTelemetry collector |
| **Event Store** | Immutable log for replay & audit | PostgreSQL logical replication, Kafka (if volume justifies) |
| **LLM / Embedding Host** | Local inference | Ollama, vLLM, llama.cpp; decision gated on GPU availability |

_For each open slot we track: current workaround, blocking factors, and acceptance criteria before lock-in._

---

## 3  Decision-Log Conventions

* **Status:** _proposed → trial → locked-in → deprecated_  
* Markdown headings match slot names for easy grep.  
* Cite research paragraphs (as we did above) so newcomers can trace decisions.

---

*Next action:* as you drop the remaining PDFs, we’ll append or adjust the corresponding slot sections using this same structure.
