# ADR Type System for RAG Research Stack

## Overview

This document defines the Architecture Decision Record (ADR) type system for the RAG research stack monorepo. The system supports research fraud detection, educational research evaluation, and agent swarm orchestration while maintaining clear separation between conceptual decisions and vendor implementations. The expanded type system enables comprehensive omni-domain research ingestion for knowledge graph construction and automated research processing at scale.

## Type System Architecture

### Core Technical Types (4)

| Code | Name | Purpose | Example Use Case |
|------|------|---------|------------------|
| `CON` | Concept | Vendor-agnostic architectural slots | Vector Store requirements definition |
| `VEN` | Vendor | Specific implementation choices | Qdrant selection with rationale |
| `ARC` | Architecture | System-wide structural decisions | Multi-agent system design |
| `INT` | Integration | Inter-component connections | API gateway patterns |

### Research & Knowledge Types (8)

| Code | Name | Purpose | Example Use Case |
|------|------|---------|------------------|
| `RSH` | Research | Literature review, comparative analysis | Graph neural network survey for fraud detection |
| `KNO` | Knowledge | Graph schema, ontology, data models | Research paper entity relationship schema |
| `ALG` | Algorithm | ML models, processing pipelines | Fraud detection classifier architecture |
| `VAL` | Validation | Testing approaches, evaluation metrics | Model performance benchmarking strategy |
| `SYN` | Synthesis | Multi-research consolidation | Backend architecture summary |
| `DAT` | Data | Schema design, modeling, migrations | Knowledge graph structure |
| `PER` | Performance | Benchmarking, optimization, scaling | Query performance analysis |
| `API` | API Design | Interface contracts, versioning | REST API specification |

### Domain-Specific Types (4)

| Code | Name | Purpose | Example Use Case |
|------|------|---------|------------------|
| `AGT` | Agent | Individual agent design decisions | Literature review agent specialization |
| `SWM` | Swarm | Multi-agent coordination patterns | Task orchestration protocol design |
| `FRD` | Fraud Detection | Domain-specific detection logic | Research fraud pattern recognition |
| `EDU` | Education | Homeschool curriculum, learning paths | Off-grid education framework design |

### User Experience & Interface Types (3)

| Code | Name | Purpose | Example Use Case |
|------|------|---------|------------------|
| `UX` | User Experience | Interface design, usability decisions | Component design patterns |
| `UI` | User Interface | Visual design, interaction patterns | Design token system |
| `ACC` | Accessibility | Accessibility compliance decisions | Screen reader compatibility |

### Business & Legal Types (4)

| Code | Name | Purpose | Example Use Case |
|------|------|---------|------------------|
| `BIZ` | Business | Revenue models, monetization | Agent-as-a-Service pricing |
| `LEG` | Legal | Compliance, licensing, regulatory | GDPR data handling requirements |
| `ETH` | Ethics | AI ethics, research integrity | Bias prevention in fraud detection |
| `LIC` | Licensing | Open source, IP management | Apache 2.0 vs MIT selection |

### Operational & Governance Types (6)

| Code | Name | Purpose | Example Use Case |
|------|------|---------|------------------|
| `SEC` | Security | Auth, encryption, privacy | API authentication strategy |
| `OPS` | Operations | Deployment, monitoring, scaling | Container orchestration approach |
| `GOV` | Governance | Data policies, ethical guidelines | Open source distribution strategy |
| `PRC` | Process | Development workflow, methodology | Research paper ingestion workflow |
| `QUA` | Quality | Code quality, testing strategies | Automated testing pipeline |
| `DOC` | Documentation | Information architecture, standards | API documentation strategy |

### Meta & Evolution Types (4)

| Code | Name | Purpose | Example Use Case |
|------|------|---------|------------------|
| `META` | Meta | ADR system itself, knowledge management | This type system definition |
| `EVO` | Evolution | Migration paths, technical debt | Database migration strategy |
| `EXP` | Experimental | Proof-of-concepts, research spikes | Novel agent architecture exploration |
| `FUT` | Future | Forward-looking analysis, trends | AI regulation trend analysis |

## Total: 33 ADR Types

### Benefits of Expanded Type System

**✅ Omni-Domain Coverage**: Handles any research domain without gaps
**✅ One-Pass Ingestion**: No need to re-process documents for missing types
**✅ Graph-Ready**: Rich typing enables sophisticated knowledge graph partitioning
**✅ Agent-Scalable**: Types support both generalist and specialist agent development
**✅ Future-Proof**: Comprehensive enough for research scaling and automation

## ADR Naming Convention

### Format
```
ADR-YYMM-TYPE-NNN[-vM.m.p]
```

### Field Definitions
- **YYMM**: Creation date (2508 = August 2025)
- **TYPE**: Three-letter type code from system above
- **NNN**: Sequential number within type (001, 002, etc.)
- **vM.m.p**: Optional semantic version for major revisions

### Examples
```
ADR-2508-CON-001        # Concept: Vector Store (base version)
ADR-2508-VEN-001        # Vendor: Qdrant implementation
ADR-2508-RSH-001        # Research: Vector DB comparison study
ADR-2508-AGT-001        # Agent: Literature review specialist
ADR-2508-UX-001         # UX: Component design patterns
ADR-2508-BIZ-001        # Business: Monetization strategy
ADR-2508-LEG-001        # Legal: GDPR compliance framework
ADR-2508-CON-001-v2.0.0 # Major revision to Vector Store concept
```

## Required Metadata Structure

### Enhanced YAML Front Matter
```yaml
---
id: ADR-YYMM-TYPE-NNN
legacy_id: [previous_id]        # For migrated ADRs
type: [TYPE_CODE]
status: [proposed|accepted|deprecated|superseded]
date: YYYY-MM-DD
title: "Brief decision description"

# Enhanced metadata for research-driven decisions
decision_confidence: [1-10]      # How certain are you about this choice
time_investment: "X_hours"       # Actual time spent researching/deciding
main_tradeoff: "aspect_a vs aspect_b"  # Key compromise made
alternatives_rejected: ["option1", "option2"]  # What you almost picked
reevaluate_when: "specific_trigger"     # Clear condition for revisiting

# Relationship tracking
supersedes: [ADR-ID]            # What this replaces
superseded_by: [ADR-ID]         # What replaces this
implements_concept: [ADR-ID]    # For VEN ADRs, link to CON ADR
research_basis: [ADR-ID]        # Link to supporting RSH ADRs

# Evidence and documentation
linked_evidence:
  - "../reference/source_document.pdf"
  - "research_analysis.md"

tags: [tag1, tag2, tag3]
---
```

**Field hygiene**
• `research_basis` must list ADR IDs only (no free-text).
• Only RSH ADRs may contain `linked_evidence:`; downstream ADRs point to research via `research_basis`.


## Relationship Patterns

### Research → Concept → Vendor Chain
```
RSH ADR (Literature Review)
    ↓ informs
CON ADR (Requirements Definition)
    ↓ drives
VEN ADR (Specific Implementation)
    ↓ enables
INT ADR (System Integration)
```

### Agent Hierarchy
```
AGT ADR (Individual Agent Design)
    ↓ composes into
SWM ADR (Swarm Coordination)
    ↓ supports
ARC ADR (System Architecture)
```

### Business & Legal Integration
```
LEG ADR (Regulatory Requirements)
    ↓ constrains
ETH ADR (Ethical Guidelines)
    ↓ guides
BIZ ADR (Business Strategy)
    ↓ drives
GOV ADR (Governance Framework)
```

## Implementation Phases

### Phase 1: Foundation (Current)
**Priority Types**: `CON`, `VEN`, `RSH`, `KNO`, `UX`, `META`, `LEG`, `ETH`

- [x] Define expanded type system (this document)
- [ ] Update validation scripts for 33 types
- [ ] Process reference documents into RSH ADRs with full type coverage
- [ ] Establish vendor selections with research backing
- [ ] Document GDPR compliance and AI ethics frameworks

### Phase 2: Intelligence (6 months)
**Priority Types**: `ALG`, `AGT`, `SWM`, `FRD`, `DAT`, `PER`, `API`

- [ ] Implement ML models based on research
- [ ] Design specialized agent architectures
- [ ] Build fraud detection algorithms
- [ ] Create swarm coordination protocols
- [ ] Establish knowledge graph schemas
- [ ] Define API contracts and performance benchmarks

### Phase 3: Distribution (12 months)
**Priority Types**: `EDU`, `GOV`, `BIZ`, `LIC`, `EVO`, `FUT`

- [ ] Educational curriculum integration
- [ ] Business model implementation
- [ ] Open source licensing strategy
- [ ] Governance frameworks for distribution
- [ ] Migration and evolution tooling
- [ ] Future trend analysis and adaptation

## Directory Structure Integration

```
docs/
├── process/
│   ├── adr-type-system.md      # This document
│   ├── branching-strategy.md   # Git workflow
│   └── github-standards.md     # Development standards
├── decisions/
│   ├── ADR-2506-UX-001.md               # Enhanced format
│   ├── ADR-2508-RSH-001.md              # Research ADRs
│   ├── ADR-2508-VEN-007.md              # Vendor selections
│   ├── ADR-2508-LEG-001.md              # Legal compliance (future)
│   └── legacy-backup-*/                 # Legacy format preserved
├── reference/
│   ├── [21 research PDFs]               # Source for RSH ADRs
│   └── research_synthesis.pdf           # Source for SYN ADRs
└── automation/
    └── ingestion_output/                # Processing tracking
```

## Validation Requirements

### Automated Checks
- Type codes must exist in approved 33-type system
- Sequential numbering unique within type
- Required metadata fields present
- Evidence links point to existing files
- Cross-references between ADRs are valid

### Quality Assurance
- All VEN ADRs must reference a CON ADR
- Research claims must link to evidence
- Vendor decisions must justify concept alignment
- Legal and ethical considerations documented for AI decisions
- Business impact assessed for major architectural choices
- Relationship mappings must be bidirectional

## Migration Strategy

### Legacy ADR Handling
1. **Preserve Legacy IDs**: Add `legacy_id` field to maintain references
2. **Cross-Reference**: Link old and new formats bidirectionally
3. **Gradual Migration**: Update high-impact decisions first
4. **No Breaking Changes**: Existing links continue to work
5. **Type Assignment**: Assign appropriate types from 33-type system to legacy ADRs

### Example Migration
```yaml
# New format maintains legacy compatibility
id: ADR-2506-UX-001
legacy_id: 0001-favicon-gradient
supersedes: 0001-favicon-gradient.md
```

### Validation Script Updates
Update automation scripts to handle all 33 types:
```bash
# Update validation to accept expanded type system
./tools/validate-fixed-adrs.sh  # Now supports all 33 types
```

## Success Metrics

- **Research Traceability**: Every technical decision traces to academic literature
- **Concept Clarity**: Clear separation between architectural concepts and implementations
- **Distribution Readiness**: External teams can understand and adopt the system
- **Evolution Support**: Changes don't lose institutional knowledge
- **Omni-Domain Coverage**: System handles all research domains without gaps
- **One-Pass Efficiency**: Documents processed once with complete type coverage
- **Graph Readiness**: Rich metadata enables sophisticated knowledge partitioning
- **Compliance Integration**: Legal and ethical considerations embedded in decision process

---

*This expanded type system enables comprehensive research-driven, modular architecture decisions that scale from solo development to distributed teams while maintaining academic rigor, legal compliance, and institutional memory. The 33-type system supports omni-domain research ingestion for knowledge graph construction and automated research processing at scale.*
