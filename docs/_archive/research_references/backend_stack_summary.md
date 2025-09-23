## 🧱 Janus Tech Stack Overview

This document tracks the selected and pending components for the Janus architecture. Each component "slot" represents a conceptual unit in the backend stack. For locked-in components, we provide the selected technology, justification, and alternatives considered. Pending components are included for ongoing evaluation.

---

### ✅ Locked-In Components

#### 🧠 Core Infrastructure

- **Primary Language**: `Python`
  - ✔️ Chosen due to ecosystem maturity, AI tooling, and stack compatibility.

- **Task Queue**: `Dramatiq`
  - ✔️ Lightweight, Pythonic API, process-based concurrency.
  - **Alternatives considered**: Celery, RQ, Huey
  - **Rationale**: Celery is heavier and requires more config overhead; RQ lacks key scheduling features. Dramatiq provides solid support for RabbitMQ with less friction.

- **Message Broker**: `RabbitMQ`
  - ✔️ Durable over fast, highly supported, decouples producers/consumers.
  - **Alternatives**: Redis Streams, Kafka, NATS
  - **Rationale**: Chosen for reliability and alignment with Dramatiq. Kafka was overkill for solo-dev.

- **Cache / Key-Value Store**: `Redis`
  - ✔️ Mature, durable if properly configured, supports Lua scripting.
  - **Alternatives**: KeyDB, DragonflyDB
  - **Rationale**: Redis is well-supported, horizontally scalable in enterprise mode. KeyDB's multi-threading was tempting but cluster trade-offs and maturity were concerns.

- **Object Storage**: `MinIO`
  - ✔️ S3-compatible, local-first, horizontally scalable.
  - **Alternatives**: SeaweedFS, Ceph, custom blob storage
  - **Rationale**: MinIO has mature S3 compatibility, enabling hybrid local/cloud data workflows.

- **Lua Scripting Layer** (within Redis)
  - ✔️ Required for job throttling, atomic coordination, and stateful agent control
  - **Rationale**: Enables lightweight resource orchestration without introducing complex external schedulers.

- **RAG Stack**: `LangChain` + `AutoGen` + `GraphRAG`
  - ✔️ Combines symbolic retrieval (GraphRAG), agent-based action planning (LangChain), and multi-agent coordination (AutoGen).
  - **Alternatives considered**: Haystack, LlamaIndex, RAGFlow
  - **Rationale**: GraphRAG naturally integrates with Neo4j. LangChain provides flexible tool integration. AutoGen enables robust multi-agent collaboration and memory.

#### 📦 Data & Persistence

- **Relational Database**: `PostgreSQL`
  - ✔️ Durable, ACID-compliant, well-supported by SQLAlchemy.
  - **Alternatives**: MySQL, SQLite, CockroachDB
  - **Rationale**: PostgreSQL provides JSONB support, extensions, and strong consistency guarantees.

- **ORM (Relational)**: `SQLAlchemy`
  - ✔️ Flexible mapping layer for schema modeling and querying.
  - **Alternatives**: Django ORM, Tortoise ORM
  - **Rationale**: SQLAlchemy offers low-level control and wide compatibility.

- **Graph Database**: `Neo4j`
  - ✔️ Suited for modeling complex relationships and knowledge graphs.
  - **Alternatives**: ArangoDB, Dgraph, TigerGraph
  - **Rationale**: Neo4j provides mature tooling and native Python integration.

- **Graph ORM**: `Neomodel`
  - ✔️ Seamless Python integration with Neo4j.

- **Vector Store**: `Qdrant`
  - ✔️ High-performance, filtering, REST/gRPC support.
  - **Alternatives**: FAISS, Weaviate, Milvus, Pinecone
  - **Rationale**: FAISS lacks metadata filtering, Pinecone is SaaS-bound. Qdrant balances performance with self-hosting.

- **File/Object Storage**: `MinIO`
  - ✔️ Reused from object storage slot

#### 🤖 Agent Execution

- **Agent Orchestrator**: `AutoGen`
  - ✔️ Dynamic multi-agent support with message protocol, tool memory.

- **Agent Tooling**: `LangChain`
  - ✔️ Tool chaining, wrappers, and context control for AutoGen

- **Graph-Enhanced Retrieval**: `GraphRAG`
  - ✔️ Augments LangChain retrieval via knowledge graph.

#### 🧪 Supporting & Utility Services

- **Redis GUI Client**: ⏳ Pending – Options: RedisInsight, Medis, Another GUI
- **System Resource Monitor**: ⚙️ Planned – Will track CPU/RAM/VRAM utilization.
- **Inference Manager**: ⚙️ Planned – Multi-backend LLM runtime controller
- **Scheduler / Job Throttler**: ⚙️ Planned – To coordinate inference job timing and resource allocation

---

### 🕓 Pending Component Slots (To Be Finalized)

#### 🔍 Model & Inference Execution

- **Embedding Generator**
  - Must support local inference (quantized + batch).
  - Will handle vectorization in RAG workflows.

- **Local LLM Execution Engine**
  - Target: llama.cpp-compatible engines (e.g., ExLLaMA, vLLM, llama-cpp-python)
  - Must support multi-GPU, streaming, and fallback logic.

- **Model Source Interface**
  - Assumed: `HuggingFace` unless replaced.

#### 🧩 Auxiliary Services

- **System Resource Monitor**
  - Ensures coordinated CPU/RAM/VRAM throttling for solo-dev hardware.

- **Scheduling & Throttling Logic**
  - Lua-scripted Redis queue w/ awareness from resource monitor.

- **Document Store**
  - Still under evaluation — must support structured retrieval w/ indexing.
  - Alternatives under consideration: MongoDB, Typesense, PostgreSQL JSONB

- **Redis GUI Client**
  - Needed for live key inspection and job queue visibility

- **Hardware Profile Config Generator**
  - Will dynamically adjust based on host specs


---

_Last updated: 2025-07-30_
