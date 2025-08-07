# Darf Intelligence Stack

**A perfect day is completing each moment of that day perfectly.**

A constitutional AI platform that operates as your digital self - making decisions within formal constraints, managing budgets autonomously, and maintaining perfect memory of every choice through a structured Architecture Decision Record (ADR) system.

## Philosophy

This system embodies digital sovereignty: an AI agent that represents you with the same intentionality you bring to each decision, operating within constitutional bounds you define, with full audit trails and fraud detection capabilities.

## Architecture Decision Records (ADRs)

The system's intelligence comes from its decision architecture - every capability, integration, and constraint is formally documented in ADRs that create an executable knowledge graph:

- **25+ interconnected ADRs** with full research traceability  
- **Research → Concept → Implementation** chain for all technical decisions
- **Constitutional framework** for agent behavior and budget constraints
- **Self-documenting evolution** as capabilities expand

See `docs/decisions/` for the complete decision corpus.

## Technical Stack

| Concern                | Technology                                           |
|------------------------|-----------------------------------------------------|
| **Decision Engine**    | ADR-driven workflows with confidence scoring        |
| **Backend Language**   | Python 3.12 (Poetry 2.1.3)                        |
| **Frontend Framework** | Next 15 · React 19 · Tailwind 4 · shadcn/UI       |
| **Message Broker**     | RabbitMQ 3                                          |
| **Task Queue**         | Dramatiq + Redis                                    |
| **Relational DB**      | PostgreSQL 15                                       |
| **Knowledge Graph**    | Neo4j 5 (Community)                                |
| **Vector Store**       | Qdrant v1                                           |
| **Object Store**       | MinIO (S3-compatible)                               |
| **Cache/Pub-sub**      | Redis 7                                             |
| **Container Runtime**  | Podman 4 + Quadlet                                 |

## Repository Structure
apps/            # Application services
backend/         # AI agent services & decision engine
frontend/        # Constitutional AI interface
packages/        # Shared libraries
shared/          # ADR parsing & workflow execution
infra/           # Infrastructure as code
docker/          # Self-hosted infrastructure
docs/            # Documentation & decisions
decisions/       # ADR corpus (authoritative)
templates/       # ADR templates
reference/       # Research materials (19 PDFs)

## Core Capabilities

### Decision Architecture
- **Formal reasoning** through structured ADR workflows
- **Evidence-based decisions** with research traceability  
- **Confidence scoring** and uncertainty acknowledgment
- **Constitutional constraints** preventing unauthorized actions

### Agent Operations
- **Budget management** with crypto wallet integration
- **Authentication gating** for major decisions via phone/biometric
- **Perfect memory** of all decisions and their rationale
- **Fraud detection** through behavioral pattern analysis

## Quick Start

```bash
git clone https://github.com/rsleiberin/darf-source.git
cd darf-source
poetry install --no-interaction
make lint test
python apps/backend/main.py