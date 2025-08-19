# Darf Intelligence Stack

**A perfect day is completing each moment of that day perfectly.**

A constitutional AI platform that operates as your digital self—making decisions within formal constraints, managing budgets autonomously, and maintaining perfect memory of every choice through a structured Architecture Decision Record (ADR) system.

---

## Philosophy

This system embodies **digital sovereignty**: an AI agent that represents you with the same intentionality you bring to each decision, operating within the constitutional bounds you define, with full audit trails and fraud-detection capabilities.

---

## Architecture Decision Records (ADRs)

The system's intelligence comes from its decision architecture—every capability, integration, and constraint is formally documented in ADRs that create an executable knowledge graph:

- **25+ interconnected ADRs** with full research traceability
- **Research → Concept → Implementation** chain for all technical decisions
- **Constitutional framework** for agent behaviour and budget constraints
- **Self-documenting evolution** as capabilities expand

Browse the corpus in `docs/decisions/`.

---

## Technical Stack

| Concern                | Technology                                           |
|------------------------|------------------------------------------------------|
| **Decision Engine**    | ADR-driven workflows with confidence scoring         |
| **Backend Language**   | Python 3.12 · Poetry 2.1.3                           |
| **Frontend Framework** | Next 15 · React 19 · Tailwind 4 · shadcn/UI          |
| **Message Broker**     | RabbitMQ 3                                           |
| **Task Queue**         | Dramatiq + Redis                                     |
| **Relational DB**      | PostgreSQL 15                                        |
| **Knowledge Graph**    | Neo4j 5 (Community)                                  |
| **Vector Store**       | Qdrant v1                                            |
| **Object Store**       | MinIO (S3-compatible)                                |
| **Cache / Pub-sub**    | Redis 7                                              |
| **Container Runtime**  | Podman 3.4+ · Quadlet                                |

---

## Repository Structure

apps/       # Application services
backend/    # AI agent services & decision engine
frontend/   # Constitutional AI interface
packages/   # Shared libraries
shared/     # ADR parsing & workflow execution
infra/      # Infrastructure as code
└─ podman/  # Local containers (compose & docs)
docker/     # Build files for CI/CD images
docs/       # Documentation & ADR type system
decisions/  # ADR corpus (authoritative)
templates/  # ADR templates
reference/  # Research materials (PDFs, CSVs)

---

## Core Capabilities

### Decision Architecture
* Formal reasoning through structured ADR workflows
* Evidence-based decisions with research traceability
* Confidence scoring and uncertainty acknowledgement
* Constitutional constraints preventing unauthorised actions

### Agent Operations
* Budget management with crypto-wallet integration
* Authentication gating for major decisions (phone / biometric)
* Perfect memory of all decisions and their rationale
* Fraud detection via behavioural-pattern analysis

---

## Local Containers (Podman)

We run local services (PostgreSQL, Neo4j, Qdrant, etc.) with **Podman**.
Follow the instructions in `infra/podman/README_podman.md` to install Podman 3.4+ on Ubuntu 20.04 and start the compose file.

```bash
# example (once Podman is installed and compose file filled in)
cd infra/podman
podman-compose up -d   # start databases
```

---

## Quick Start

```bash
git clone https://github.com/rsleiberin/darf-source.git
cd darf-source

# install Python deps
poetry install --no-interaction

# lint & test
make lint test

# run backend (draft)
python apps/backend/main.py
```

---

*Empowering individuals with sovereign, auditable AI—one perfectly-documented decision at a time.*

**Notes**

* The stack table lists Podman **3.4+** because that’s what installs cleanly on Ubuntu 20.04; you can bump the version when you upgrade the OS or move to Snap builds.
* The “Local Containers (Podman)” section points contributors to `infra/podman/` for compose files and install docs—aligning with your new branch.

Commit this updated README on `infra-podman-init` (or a fresh branch) before opening the PR.

---

## 🚀 Project Status

### Phase 0: Foundation ✅ COMPLETE
- [x] Issue #40: PostgreSQL setup in Podman
- [x] Issue #41: SQLAlchemy smoke test passing
- [x] Issue #42: Fixed pyproject.toml parse error
- [x] Issue #43: Research artifact retained in docs/reference
- [ ] Issue #44: PR for db-postgres-standup branch (pending)

### Recent Achievements
- **PostgreSQL 15** running in Podman on port 5432
- **SQLAlchemy** connection verified with CRUD operations
- **Project structure** fixed - all linting passing
- **38 GitHub issues** created covering complete ADR modernization roadmap

---

*Last updated: 2025-08-07*

## RAG Foundation Sprint Overview

During the RAG Foundation sprint, the team completed a series of improvements to both the backend and developer environment:

- Refactored `apps/backend/main.py` to remove inline class fields and one‑line function bodies, satisfying Ruff’s E701/E702 lint rules.
- Migrated to the new `langchain_community` packages and replaced deprecated `Qdrant` and `OpenAIEmbeddings` imports with `QdrantClient` and their community equivalents.
- Expanded `rag_query` with robust exception handling and return type annotations.
- Installed missing dependencies (`langchain-community`, `qdrant-client`, `tiktoken`, `psycopg2-binary`) and updated the lockfile to reflect these.
- Added CI-friendly behavior for the PostgreSQL connection test by skipping it when the `CI` environment variable is set.
- Added a `.env.example` file and updated `.gitignore` to exclude `node_modules/` and `.turbo/` directories.
- Removed Podman-specific artefacts and updated container documentation for Qdrant and Neo4j services.
- Ensured that all tests pass (`pytest`), type checks succeed (`mypy`), and lint issues are resolved (`ruff`) before merging.
