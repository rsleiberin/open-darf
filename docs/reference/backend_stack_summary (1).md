## 🧠 Janus System Design Brief
(High-Capacity Agent Handoff Summary)  
Date: 2025-07-31  
Author: High-Capacity 4o Agent  
Source Stack Document: backend_stack_overview.md

### 🎯 Project Vision: “A Scalable, Offline-First Personal Intelligence Architecture”
Janus is a long-term project designed to build a fully self-hosted, modular AI ecosystem that empowers the solo developer and can later scale to small distributed clusters. It aims to simulate a multi-agent cognitive framework—grounded in structured knowledge graphs, local language model execution, and human-aligned design principles.

**Primary Objectives:**
- **Offline-first + Cloud-optional**: Must run on local hardware and scale outward only as necessary.
- **Multi-agent by default**: Enables isolated or coordinated task flows for agents across a compute mesh.
- **Semantic, structured, and searchable memory**: Graph-first design augments relational, vector, and document stores.
- **Testbed for model evaluation**: Supports interchangeable embeddings and LLMs, benchmarking them against real-world agent workflows.
- **Durable & modular**: Each component serves a defined role with clean boundaries and justifications.

### 🏗️ Architectural Philosophy
The Janus backend uses a "slot-based" architecture: each conceptual function (e.g., messaging, caching, semantic memory) has a designated component that fills it. These are chosen based on:

- **Durability over speed**
- **Self-hostability over SaaS**
- **Agent compatibility over developer ease**
- **Extensibility over rigidity**

The design favors clean data pathways, full job lifecycle control, and human-level comprehension of systems—not black-box orchestration.

---

## 🧱 Janus Tech Stack Overview

This document tracks the selected and pending components for the Janus architecture. Each component "slot" represents a conceptual unit in the backend stack. For locked-in components, we provide the selected technology, justification, and alternatives considered. Pending components are included for ongoing evaluation.

---

### ✅ Locked-In Components

#### 🧠 Core Infrastructure

- **Primary Language**: `Python`
  - Chosen due to ecosystem maturity, AI tooling, and stack compatibility.

- **Task Queue**: `Dramatiq`
  - ✔️ Lightweight, Pythonic API, process-based concurrency.
  - Alternatives considered: Celery, RQ, Huey
  - Rationale: Celery is heavier and requires more config overhead; RQ lacks key scheduling features. Dramatiq provides solid support for RabbitMQ with less friction.

- **Message Broker**: `RabbitMQ`
  - ✔️ Durable over fast, highly supported, decouples producers/consumers.
  - Alternatives: Redis Streams, Kafka, NATS
  - Rationale: Chosen for reliability and alignment with Dramatiq. Kafka was overkill for solo-dev.

- **Cache / Key-Value Store**: `Redis`
  - ✔️ Mature, durable if properly configured, supports Lua scripting.
  - Alternatives: KeyDB, DragonflyDB
  - Rationale: Redis is well-supported, horizontally scalable in enterprise mode. KeyDB's multi-threading was tempting but cluster trade-offs and maturity were concerns.

- **Object Storage (S3-compatible)**: `MinIO`
  - ✔️ Local-first, S3 API compatible, horizontally scalable
  - Alternatives: SeaweedFS, Ceph, custom blob storage
  - Rationale: MinIO has mature S3 compatibility and supports cloud & local storage workflows.

- **Lua Scripting Layer (within Redis)**
  - ✔️ Required for job throttling, atomic coordination, and stateful agent control
  - Used for lightweight coordination without a full-blown scheduler

- **RAG Stack**: `LangChain` + `AutoGen` + `GraphRAG`
  - ✔️ GraphRAG integrates naturally with our Neo4j stack.
  - ✔️ LangChain provides a rich agent/action toolkit.
  - ✔️ AutoGen supports multi-agent collaboration and dynamic tool orchestration.
  - Rationale: This trio enables document-driven grounding, multi-agent task flow, and code integration.

- **Containerization**: `Podman` + `Quadlet`
  - ✔️ Secure, rootless container management with systemd integration
  - Rationale: Podman is a Docker alternative focused on system security; Quadlet allows declarative, system-native service definitions.

- **Orchestration Layer**: `Kubernetes`
  - ✔️ Chosen for future-proof scalability and multi-node orchestration
  - Rationale: Offers workload distribution and orchestration over many agents/devices

#### 📦 Data & Persistence

- **Relational Database**: `PostgreSQL`
  - ✔️ Durable, ACID-compliant, well-supported by SQLAlchemy

- **ORM (Relational)**: `SQLAlchemy`
  - ✔️ Flexible mapping layer for schema modeling and querying

- **Graph Database**: `Neo4j`
  - ✔️ Supports complex relationships and reasoning

- **Graph ORM**: `Neomodel`
  - ✔️ Pythonic integration with Neo4j

- **Vector Store**: `Qdrant`
  - ✔️ Chosen for performance, filtering, and native gRPC/REST interfaces
  - Alternatives: FAISS, Weaviate, Milvus, Pinecone
  - Rationale: FAISS lacks filtering; Pinecone is proprietary. Qdrant offers self-hosting and hybrid retrieval.

- **File Storage**: `MinIO`
  - ✔️ S3-compatible, reuses object storage

#### 🧩 Agent Architecture

- **Agent Execution Framework**: `AutoGen`
  - ✔️ Modular multi-agent orchestration, integrates with LangChain

- **RAG Tooling**: `LangChain` + `GraphRAG`
  - ✔️ Tool wrappers, agent chains, graph-augmented grounding

- **Tool Use Management**: `LangChain`
  - ✔️ Provides integration for tool execution wrappers

- **Lua Coordination Layer**: `Redis Lua Scripting`
  - ✔️ Enables atomic job coordination and throttling across workers

---

### 🕓 Pending Component Slots (To Be Finalized)

#### 🧠 Model & Inference Execution

- **Embedding Generator**
  - Must support local inference (quantized + batch)
  - Will assist with vectorization in RAG workflows

- **Local LLM Execution Engine**
  - Targeting llama.cpp-compatible engines (e.g., ExLLaMA, vLLM)
  - Requires token streaming, multi-GPU support, and fallback

- **Model Source Interface**
  - `HuggingFace` assumed unless replaced

#### 📦 Persistence Extensions

- **Document Store**
  - For raw, unstructured JSON ingestion prior to processing

- **Event Store**
  - To record audit trails and system-level activities

- **Time-Series Store**
  - For logging physiological or sensor data over time

#### 🧩 Coordination & Monitoring

- **Resource Monitor**
  - For CPU/RAM/VRAM live tracking and throttling

- **Scheduling & Throttling Logic**
  - Governs task prioritization, load balancing, and rate-limiting logic

- **Redis GUI Client**
  - Options: RedisInsight, Medis, Another GUI

#### 📦 Container & DevOps Layer

- **Container Monitoring**
  - Tools like cAdvisor, Prometheus, or Grafana for live metrics

- **Centralized Logging Layer**
  - Tools like Loki, FluentBit, or ELK stack for container and service logs

- **Container Registry**
  - Local registry for storing container images (e.g., Harbor, Docker Registry)

---

_Last updated: 2025-07-31_

