# Darf‑Tech ‒ Backend Stack Overview

> **Goal**  Design a resilient, mostly self‑hostable agent‑orchestration platform that can run **off‑grid** on local hardware yet scale horizontally or burst to managed services when required.

---
## ✅ Locked‑In Core Components  
*(Each chosen after deep comparative research)*

| Category | Technology | Purpose | Key Rationale |
|---|---|---|---|
| **Relational DB** | **PostgreSQL + (SQLAlchemy / Alembic)** | Canonical structured data, auth, audit | Mature ACID DB, rich ecosystem, works offline, first‑class async libraries |
| **Graph DB** | **Neo4j (OSS)** | Long‑term semantic memory & knowledge graph | Powerful Cypher queries, tight Python driver support. *Licensing concerns parked* – Community Edition sufficient for solo/offline use. |
| **Vector DB** | **Qdrant** | High‑dimensional similarity search (RAG) | Lightweight Rust core, local‑first, GPU/AVX support, live filters |
| **Message Broker** | **RabbitMQ** | Reliable job dispatch | Stable, durable queues, fits Dramatiq actors; can run on low‑power SBCs |
| **Task Queue** | **Dramatiq** | Background & scheduled work | Simple actor model, automatic retries, RabbitMQ adapter |
| **KV Cache / Session** | **Redis** | Fast token/session & pub‑sub | Separates transient data from durable MQ; avoids "all‑in‑one" coupling |
| **Object Store** | **MinIO** | S3‑compatible binary storage | Single‑binary deploy, erasure‑coding, self‑host friendly |
| **RAG Tooling** | **LangChain + AutoGen + GraphRAG** | Orchestration, multi‑agent loops, hybrid retrieval | Modular, language‑agnostic tool chains, integrates with Postgres / Neo4j / Qdrant |

---
## 🟡 Pending Capability Slots (to be filled after targeted research)

| Slot | Purpose | Notes / Candidate Families |
|---|---|---|
| **Local Embedding Generator** | Generate dense vectors offline (versatile across CPU/GPU) | HF Transformers, Sentence‑Transformers, GGUF models… |
| **Local *Off‑the‑Grid* LLM Engine** | Run OSS LLMs with no internet | vLLM, llama.cpp, ollama, exllamav2… |
| **Document Store** | Staging dump for unprocessed files & JSON blobs distinct from durable object store | CouchDB (replication), LiteFS, Mongo Community… |
| **Time‑Series DB** | Metrics, physiological sensor data | TimescaleDB (fits Postgres cluster), Influx, VictoriaMetrics |
| **Event Store** | Immutable audit / CQRS stream | EventStoreDB, Postgres commit‑log table, RedisStreams + Deltas |
| **Unified Access API** | Abstract multi‑store queries for agents | FastAPI gateway, Hasura GraphQL federation, custom GRPC service |
| **Observability Suite** | Logs, metrics & traces | Loki + Grafana, OpenTelemetry collector, Prometheus + Alertmanager |
| **Configuration & Secrets Management** | Centralized config, keyed secrets for multi‑node deployments | HashiCorp Vault, Doppler, SOPS + Git, env‑seer |
| **Data Ingestion Orchestrator / ETL** | Declarative pipelines for scraping, parsing & load | Airbyte, Dagster, Apache NiFi, Meltano |
| **Experiment Tracking & Model Registry** | Reproducible ML runs, versioned artifacts | MLflow, Weights & Biases (self‑host), DVC Experiments |
| **Identity & Access Management** | AuthN/AuthZ for UI dashboards & agents | Keycloak, Authentik, Ory Kratos/Hydra |
| **Backup & Disaster Recovery** | Automated secure snapshots of DBs & object store | Restic, Velero (K8s), BorgBackup + cron |
| **Edge Deployment / Hardware Abstraction** | Uniform runtime across local ARM boards & servers; GPU/TPU toggles | Docker‑Compose profiles, NixOS flakes, K3s + Rook‑Ceph |

_Add additional rows as new architecture questions surface.__

---
## Key Design Decisions & Trade‑offs

* **Separate MQ (RabbitMQ) vs. Redis‑Streams** — RabbitMQ chosen for stronger delivery guarantees & back‑pressure control. Redis retained strictly for low‑latency cache / pub‑sub where its single‑thread limitations are acceptable.
* **Neo4j Licensing** — Community Edition suffices for offline/solo R&D; commercial upgrade evaluated only if multi‑tenant SaaS pivots later. No blocker for local deployment.
* **Resilience First** — All locked‑in components have container images, ARM builds, and documented offline install paths. Goal: run the full stack on a rugged mini‑PC with solar‑backed UPS.

---
