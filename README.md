# Darf Intelligence Stack

**Constitutional AI Platform for Digital Sovereignty**

*A perfect day is completing each moment of that day perfectly.*

A Constitutional AI platform that operates as your digital self, making decisions within formal mathematical constraints while preserving individual sovereignty. The system provides autonomous decision-making with constitutional compliance, comprehensive audit trails, and structured Architecture Decision Records (ADRs) that create an executable knowledge graph.

---

## Architecture Overview

The Darf Intelligence Stack implements a constitutional AI consciousness interface architecture that preserves user sovereignty while enabling beneficial AI assistance. The system operates through formal constitutional constraints that ensure every AI operation enhances rather than diminishes individual agency.

### Core Principles

**Digital Sovereignty**: AI agents represent users with the same intentionality users bring to decisions, operating within constitutional bounds users define while maintaining full audit trails and verification capabilities.

**Constitutional Compliance**: Mathematical frameworks ensure all system operations preserve user autonomy through formal verification of decision-making processes and sovereignty preservation guarantees.

**Decision Architecture**: Structured ADR system creates executable knowledge graphs where every capability, integration, and constraint receives formal documentation with complete research traceability.

---

## Technology Stack

| Concern                | Technology                                           |
|------------------------|------------------------------------------------------|
| **Constitutional Engine** | TLA+ formal verification with sovereignty preservation |
| **Decision Engine**    | ADR-driven workflows with confidence scoring         |
| **Backend Language**   | Python 3.12 · Poetry 2.1.3                         |
| **Frontend Framework** | Next 15 · React 19 · Tailwind 4 · shadcn/UI        |
| **Message Broker**     | RabbitMQ 3 · Dramatiq + Redis task queuing          |
| **Relational Database** | PostgreSQL 15                                        |
| **Knowledge Graph**    | Neo4j 5 Community (Constitutional Schema)           |
| **Vector Store**       | Qdrant v1 (Semantic Search)                         |
| **Object Store**       | MinIO S3-compatible (Content-Addressable)           |
| **Cache & Pub-sub**    | Redis 7                                              |
| **Container Runtime**  | Podman 3.4+ · Quadlet                               |

---

## Repository Structure

This turborepo monorepo is organized to support scalable development across multiple applications and shared packages:

```
apps/                   # Application services
├── backend/           # Constitutional AI agent services & decision engine
└── frontend/          # Constitutional AI interface
packages/              # Shared libraries and utilities
├── shared/            # ADR parsing & workflow execution
├── tla/               # Formal verification specifications
└── constitutional/    # Sovereignty preservation protocols
infra/                 # Infrastructure as code
├── podman/            # Local development containers
└── kubernetes/        # Production deployment manifests
docker/                # Container build configurations
docs/                  # Documentation and specifications
├── decisions/         # ADR corpus (authoritative)
├── templates/         # ADR templates
├── audit/             # Performance receipts and validation logs
└── api/               # API documentation
```

---

## Getting Started

### Prerequisites

- Node.js 18+ and npm 9+
- Python 3.12+ and Poetry 2.1.3+
- Podman 3.4+ (for local services)
- Git 2.40+

### Local Development Setup

```bash
# Clone the repository
git clone https://github.com/rsleiberin/darf-source.git
cd darf-source

# Install all dependencies
npm install

# Start local services (PostgreSQL, Neo4j, Qdrant, Redis, MinIO)
cd infra/podman
podman-compose up -d

# Install Python dependencies
poetry install --no-interaction

# Run development servers
npm run dev
```

### Verification

```bash
# Run all tests
npm run test

# Run linting
npm run lint

# Type checking
npm run type-check

# Python-specific testing
poetry run pytest
```

---

## Development Workflow

### Architecture Decision Records

All significant decisions are documented through structured ADRs that create an executable knowledge graph. Each ADR follows the research-to-concept-to-implementation chain with full traceability and constitutional compliance verification.

Browse existing ADRs in `docs/decisions/` and use templates in `docs/templates/` for new decisions.

### Constitutional Compliance

All development must maintain constitutional compliance verification through formal mathematical frameworks. The TLA+ specifications in `packages/tla/` provide formal verification requirements for sovereignty preservation properties.

Development workflow includes constitutional compliance gates through automated CI checks that verify mathematical sovereignty preservation throughout implementation processes.

### Performance Requirements

The system maintains validated performance targets including constitutional compliance verification under 170ms, semantic search capabilities under 120ms, and multi-agent coordination under 500ms. All implementations must demonstrate performance compliance through comprehensive benchmarking protocols.

---

## Core Capabilities

### Constitutional Agent Operations

The system provides autonomous decision-making within formal constitutional constraints, comprehensive audit trails with perfect decision memory, fraud detection through behavioral pattern analysis, and mathematical sovereignty preservation guarantees throughout all operations.

Agent capabilities include budget management with crypto-wallet integration, authentication gating for major decisions, preference learning without sovereignty violation, and decision recommendation with constitutional compliance verification.

### Formal Verification Framework

TLA+ specifications provide mathematical proof of sovereignty preservation properties while enabling systematic formal verification of constitutional compliance across all system operations. The verification framework supports distributed deployment scenarios with Byzantine fault tolerance and democratic legitimacy preservation.

---

## Contributing

### Development Standards

All contributions must maintain constitutional compliance verification as the primary optimization criterion while following established coding standards through automated linting and type checking. Implementation requires comprehensive testing with constitutional compliance validation at all development checkpoints.

### Pull Request Process

Pull requests must include constitutional compliance verification, performance impact assessment, comprehensive test coverage, and ADR documentation for architectural decisions. The CI system enforces label requirements and policy gates to maintain systematic governance throughout development advancement.

### Code Organization

Follow the established monorepo structure with clear separation between applications, shared packages, and infrastructure components. Maintain constitutional compliance integration throughout all development workflows with formal verification requirements documented in TLA+ specifications.

---

## Project Status

### Current Development Phase

**Phase 1 Foundation**: Constitutional constraint validation engine implementation with systematic integration of Neo4j constitutional schema validation, real-time constraint checking protocols, and mathematical sovereignty preservation verification systems.

**Infrastructure**: PostgreSQL 15 operational with SQLAlchemy integration, comprehensive CI governance with policy enforcement, and systematic development discipline through comprehensive GitHub issue tracking.

**Recent Achievements**: Project structure optimization with all linting requirements satisfied, RAG foundation implementation with langchain integration, and comprehensive workflow automation through policy gates and documentation ownership protection.

### Immediate Priorities

Constitutional constraint validation engine development represents the primary implementation focus with Neo4j constitutional schema integration, sub-170ms performance requirements, and comprehensive testing frameworks for operational deployment validation.

Enhanced development workflow optimization includes TLA+ formal verification integration, systematic constitutional compliance verification protocols, and preparation for expanded monorepo operations supporting future scalability requirements.

---

## Documentation

Comprehensive documentation is maintained in the `docs/` directory including architecture specifications, API documentation, deployment guides, and constitutional compliance frameworks. The ADR system in `docs/decisions/` provides complete decision traceability with research foundations.

For detailed technical specifications, formal verification requirements, and constitutional compliance protocols, refer to the comprehensive documentation structure that supports systematic development advancement and operational deployment guidance.

---

## License

This project implements constitutional AI frameworks with mathematical sovereignty preservation guarantees. See LICENSE file for terms and conditions regarding usage, modification, and distribution of constitutional AI implementations.

---

*Empowering individuals with sovereign, auditable AI through systematic constitutional compliance verification and consciousness interface architecture.*

**Repository**: [https://github.com/rsleiberin/darf-source](https://github.com/rsleiberin/darf-source)

*Last updated: August 19, 2025*