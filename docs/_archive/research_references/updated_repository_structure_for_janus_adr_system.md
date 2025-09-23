> ⚠️ Examples only — not runnable
> This document contains illustrative/math/pseudo code. Do not execute in production.

## Updated Repository Structure for Janus ADR System

Based on your locked-in backend stack and monorepo requirements, here's the evolved architecture:

```text
janus-source/                           # Turborepo root
├── turbo.json                         # Turborepo configuration
├── package.json                       # Root package.json with workspaces
├── .env.example                       # Environment variables template
│
├── apps/                               # Turborepo apps workspace
│   ├── backend/                       # FastAPI backend (existing)
│   │   ├── main.py
│   │   └── api/
│   │       ├── decisions.py          # ADR REST endpoints
│   │       ├── triggers.py           # Trigger management
│   │       └── cascades.py           # Cascade monitoring
│   │
│   ├── adr-orchestrator/             # NEW: ADR decision orchestrator
│   │   ├── __init__.py
│   │   ├── main.py                   # Dramatiq worker entry point
│   │   ├── tasks/
│   │   │   ├── decision_tasks.py     # Dramatiq tasks for ADR processing
│   │   │   ├── cascade_tasks.py      # Cascade execution tasks
│   │   │   └── ingestion_tasks.py    # Document ingestion tasks
│   │   │
│   │   ├── agents/                   # AutoGen agent definitions
│   │   │   ├── decision_agent.py     # ADR generation agent
│   │   │   ├── classification_agent.py # Taxonomy classification agent
│   │   │   ├── validation_agent.py   # Constitutional validation agent
│   │   │   └── blockchain_agent.py   # Blockchain integration agent
│   │   │
│   │   ├── workflows/
│   │   │   ├── htn_planner.py       # HTN planning with AutoGen
│   │   │   ├── bdi_reactor.py       # BDI reactive patterns
│   │   │   └── saga_coordinator.py   # Distributed transaction sagas
│   │   │
│   │   └── config/
│   │       ├── dramatiq_config.py    # Dramatiq + RabbitMQ setup
│   │       └── autogen_config.py     # AutoGen agent configurations
│   │
│   └── adr-monitor/                   # NEW: System monitoring service
│       ├── main.py                   # Monitoring service entry
│       ├── metrics.py                # Prometheus metrics collection
│       └── dashboards/               # Grafana dashboard configs
│
├── packages/                          # Turborepo packages workspace
│   ├── adr-core/                     # Core ADR business logic
│   │   ├── pyproject.toml           # Package dependencies
│   │   ├── src/
│   │   │   ├── models/
│   │   │   │   ├── sqlalchemy/      # SQLAlchemy models
│   │   │   │   │   ├── adr.py      # ADR relational model
│   │   │   │   │   ├── cascade.py  # Cascade execution tracking
│   │   │   │   │   └── event.py    # Event sourcing model
│   │   │   │   │
│   │   │   │   ├── neomodel/        # Neo4j graph models
│   │   │   │   │   ├── decision_graph.py  # Decision dependency graph
│   │   │   │   │   ├── trigger_chain.py   # Trigger cascade paths
│   │   │   │   │   └── knowledge_graph.py # Integration with GraphRAG
│   │   │   │   │
│   │   │   │   └── qdrant/          # Vector models
│   │   │   │       ├── embeddings.py      # ADR embeddings
│   │   │   │       └── context_vectors.py # Context similarity
│   │   │   │
│   │   │   ├── classification/
│   │   │   │   ├── taxonomy.py      # Dynamic taxonomy with Redis
│   │   │   │   ├── drift_detector.py # Concept drift detection
│   │   │   │   └── evolution.py     # Auto-evolution with Lua scripts
│   │   │   │
│   │   │   ├── confidence/
│   │   │   │   ├── mcda.py         # Multi-criteria analysis
│   │   │   │   ├── evidence.py     # Dempster-Shafer implementation
│   │   │   │   └── validators.py   # Constitutional constraints
│   │   │   │
│   │   │   └── storage/
│   │   │       ├── postgres_adapter.py  # PostgreSQL via SQLAlchemy
│   │   │       ├── neo4j_adapter.py    # Neo4j via Neomodel
│   │   │       ├── qdrant_adapter.py   # Qdrant vector operations
│   │   │       ├── redis_adapter.py    # Redis caching/coordination
│   │   │       └── minio_adapter.py    # MinIO document storage
│   │   │
│   │   └── tests/
│   │
│   ├── adr-langchain/                # NEW: LangChain integration package
│   │   ├── pyproject.toml
│   │   ├── src/
│   │   │   ├── tools/
│   │   │   │   ├── adr_tool.py     # ADR creation/query tool
│   │   │   │   ├── cascade_tool.py  # Cascade execution tool
│   │   │   │   └── search_tool.py   # GraphRAG search tool
│   │   │   │
│   │   │   ├── chains/
│   │   │   │   ├── decision_chain.py    # Decision-making chain
│   │   │   │   ├── validation_chain.py  # Validation chain
│   │   │   │   └── ingestion_chain.py   # Document ingestion chain
│   │   │   │
│   │   │   └── agents/
│   │   │       └── adr_agent.py    # LangChain ADR agent wrapper
│   │   │
│   │   └── tests/
│   │
│   ├── adr-graphrag/                 # NEW: GraphRAG integration
│   │   ├── pyproject.toml
│   │   ├── src/
│   │   │   ├── indexer.py          # Graph indexing with Neo4j
│   │   │   ├── retriever.py        # Hybrid retrieval (Neo4j + Qdrant)
│   │   │   ├── chunker.py          # Document chunking strategies
│   │   │   └── query_engine.py     # GraphRAG query optimization
│   │   │
│   │   └── tests/
│   │
│   ├── adr-dramatiq/                 # NEW: Dramatiq task definitions
│   │   ├── pyproject.toml
│   │   ├── src/
│   │   │   ├── actors/
│   │   │   │   ├── decision_actor.py    # ADR processing actor
│   │   │   │   ├── ingestion_actor.py   # Document ingestion actor
│   │   │   │   └── cascade_actor.py     # Cascade execution actor
│   │   │   │
│   │   │   ├── middleware/
│   │   │   │   ├── rate_limiter.py     # Redis-based rate limiting
│   │   │   │   ├── circuit_breaker.py  # Circuit breaker pattern
│   │   │   │   └── backpressure.py     # Backpressure control
│   │   │   │
│   │   │   └── brokers/
│   │   │       └── rabbitmq_broker.py  # RabbitMQ configuration
│   │   │
│   │   └── tests/
│   │
│   └── adr-redis-lua/                # NEW: Redis Lua scripts package
│       ├── pyproject.toml
│       ├── src/
│       │   ├── scripts/
│       │   │   ├── cascade_control.lua    # Cascade execution control
│       │   │   ├── rate_limiter.lua       # Token bucket rate limiting
│       │   │   ├── taxonomy_evolution.lua # Atomic taxonomy updates
│       │   │   └── confidence_scoring.lua # Distributed confidence calc
│       │   │
│       │   └── client.py            # Python client for Lua scripts
│       │
│       └── tests/
│
├── services/                         # Containerized microservices
│   ├── adr-decision-engine/         # Core decision processing
│   │   ├── Dockerfile              # Podman-compatible container
│   │   ├── decision-engine.container # Quadlet service definition
│   │   ├── main.py
│   │   └── requirements.txt
│   │
│   ├── adr-classification/          # Classification service
│   │   ├── Dockerfile
│   │   ├── classification.container
│   │   ├── main.py
│   │   └── requirements.txt
│   │
│   └── adr-graphrag/                # GraphRAG service
│       ├── Dockerfile
│       ├── graphrag.container
│       ├── main.py
│       └── requirements.txt
│
├── infrastructure/                   # Infrastructure as Code
│   ├── kubernetes/                  # K8s manifests
│   │   ├── namespaces/
│   │   ├── deployments/
│   │   ├── services/
│   │   └── configmaps/
│   │
│   ├── quadlet/                     # Systemd/Quadlet definitions
│   │   ├── adr-orchestrator.container
│   │   ├── adr-monitor.container
│   │   └── redis-lua.container
│   │
│   └── terraform/                   # Optional IaC for cloud deployment
│
├── migrations/                       # Database migrations
│   ├── alembic/                    # SQLAlchemy/Alembic migrations
│   │   ├── alembic.ini
│   │   └── versions/
│   │
│   ├── neo4j/                      # Neo4j migrations
│   │   └── cypher/
│   │
│   └── redis/                      # Redis Lua script deployment
│
├── scripts/                         # Operational scripts
│   ├── migrate_legacy_adrs.py     # Migrate 25 existing ADRs
│   ├── process_reference_docs.py  # Process 19 PDFs via MinIO
│   ├── deploy_lua_scripts.py      # Deploy Redis Lua scripts
│   └── validate_autogen_agents.py # Test AutoGen configurations
│
├── config/                          # Configuration files
│   ├── adr/
│   │   ├── htn_domains.yaml       # HTN domain definitions
│   │   ├── trigger_rules.yaml     # Trigger configurations
│   │   └── constitutional.yaml    # Constitutional constraints
│   │
│   ├── autogen/
│   │   ├── agent_configs.yaml     # AutoGen agent definitions
│   │   └── workflow_configs.yaml  # Multi-agent workflows
│   │
│   └── dramatiq/
│       ├── broker_config.yaml     # RabbitMQ settings
│       └── worker_config.yaml     # Worker configurations
│
└── docs/
    ├── decisions/                  # Existing ADRs
    ├── architecture/
    │   ├── adr_system_design.md  # This system's architecture
    │   ├── integration_guide.md  # How ADR integrates with Janus
    │   └── migration_plan.md     # Step-by-step migration
    │
    └── handoff/
        └── implementation_handoff.md # Coding agent handoff doc
```

## Implementation Handoff for Coding Agent

### Context & Objective

You're implementing an **intelligent ADR (Architecture Decision Record) system** that transforms the current manual 33-code taxonomy into a self-evolving, multi-agent decision architecture. This system will integrate seamlessly with the existing Janus backend stack while adding sophisticated decision-making capabilities.

### Key Integration Points with Existing Stack

1. **Dramatiq + RabbitMQ**: All ADR processing happens as Dramatiq tasks
2. **AutoGen + LangChain**: ADR generation uses AutoGen agents with LangChain tools
3. **GraphRAG + Neo4j**: Decision retrieval leverages existing graph infrastructure
4. **Redis + Lua**: Atomic operations for cascade control and rate limiting
5. **MinIO**: Store PDFs and generated ADRs as objects
6. **PostgreSQL + SQLAlchemy**: Event sourcing and audit trails
7. **Qdrant**: Semantic search for similar decisions

### Implementation Phases

#### Phase 1: Core Infrastructure (Week 1-2)
```text
# 1. Set up Dramatiq actors for ADR processing
# packages/adr-dramatiq/src/actors/decision_actor.py
import dramatiq
from dramatiq.brokers.rabbitmq import RabbitmqBroker

broker = RabbitmqBroker(url="amqp://rabbitmq:5672")
dramatiq.set_broker(broker)

@dramatiq.actor
def process_adr_trigger(trigger_event):
    """Process ADR trigger event through HTN planner"""
    # Implement HTN decomposition
    # Call AutoGen agents for decision generation
    # Store in PostgreSQL via SQLAlchemy
    pass

# 2. Create SQLAlchemy models
# packages/adr-core/src/models/sqlalchemy/adr.py
class ADR(Base):
    __tablename__ = 'adrs'

    id = Column(UUID, primary_key=True)
    code = Column(String(10), unique=True)  # e.g., 'RSH-001'
    trigger_rules = Column(JSONB)  # Trigger configuration
    confidence_score = Column(Float)
    cascade_depth = Column(Integer)
    # ... rest of schema from research

# 3. Deploy Redis Lua scripts
# packages/adr-redis-lua/src/scripts/cascade_control.lua
-- Atomic cascade execution control
local cascade_key = KEYS[1]
local max_depth = tonumber(ARGV[1])
local current_depth = redis.call('HINCRBY', cascade_key, 'depth', 1)
if current_depth > max_depth then
    return redis.error_reply('Max cascade depth exceeded')
end
-- Continue cascade logic
```

#### Phase 2: AutoGen Integration (Week 3-4)
```text
# apps/adr-orchestrator/agents/decision_agent.py
from autogen import AssistantAgent, UserProxyAgent
from langchain.tools import Tool

class ADRDecisionAgent:
    def __init__(self):
        self.assistant = AssistantAgent(
            name="adr_generator",
            system_message="""You are an ADR generation specialist.
            Use HTN decomposition to break down complex decisions."""
        )

        self.tools = [
            Tool(name="query_similar_adrs", func=self.query_similar),
            Tool(name="check_constraints", func=self.validate_constitutional),
            Tool(name="calculate_confidence", func=self.calculate_mcda_score)
        ]

    async def generate_adr(self, context):
        # Use GraphRAG to find relevant context
        relevant_docs = await self.graphrag_retrieve(context)

        # Generate decision with AutoGen
        response = await self.assistant.generate_reply(
            messages=[{"role": "user", "content": context}],
            tools=self.tools
        )

        # Validate and store
        return self.validate_and_store(response)
```

#### Phase 3: GraphRAG Enhancement (Week 5-6)
```text
# packages/adr-graphrag/src/retriever.py
from neo4j import GraphDatabase
from qdrant_client import QdrantClient

class HybridADRRetriever:
    def __init__(self):
        self.neo4j = GraphDatabase.driver("bolt://neo4j:7687")
        self.qdrant = QdrantClient(host="qdrant", port=6333)

    async def retrieve(self, query, k=5):
        # 1. Vector similarity from Qdrant
        vector_results = await self.qdrant.search(
            collection_name="adr_embeddings",
            query_vector=embed(query),
            limit=k*2
        )

        # 2. Graph context from Neo4j
        with self.neo4j.session() as session:
            graph_results = session.run("""
                MATCH (a:ADR)-[r:TRIGGERS|DEPENDS_ON*1..3]-(related:ADR)
                WHERE a.id IN $ids
                RETURN related
            """, ids=[r.id for r in vector_results])

        # 3. Combine and rank
        return self.rank_results(vector_results, graph_results)
```

#### Phase 4: Migration & Testing (Week 7-8)
```text
# scripts/migrate_legacy_adrs.py
async def migrate_legacy_adrs():
    """Migrate 25 existing ADRs to new system"""

    # 1. Parse existing ADRs
    legacy_adrs = parse_legacy_adrs("docs/decisions/")

    # 2. Generate embeddings
    for adr in legacy_adrs:
        adr.embedding = generate_embedding(adr.content)

    # 3. Extract implicit triggers
    for adr in legacy_adrs:
        adr.triggers = extract_triggers_with_llm(adr)

    # 4. Build dependency graph
    graph = build_dependency_graph(legacy_adrs)

    # 5. Store in new system
    await store_in_postgres(legacy_adrs)
    await store_in_neo4j(graph)
    await store_in_qdrant([a.embedding for a in legacy_adrs])

    print(f"Migrated {len(legacy_adrs)} ADRs successfully")
```

### Critical Implementation Notes

1. **Use existing Redis Lua coordination** for atomic operations
2. **Leverage Dramatiq's retry mechanisms** for fault tolerance
3. **Integrate with existing RabbitMQ topics** for event distribution
4. **Store documents in MinIO** using existing S3-compatible APIs
5. **Use Neomodel** for graph operations (already in stack)
6. **Deploy as Quadlet containers** for systemd integration

### Testing Strategy

1. **Unit tests** for each package in Turborepo
2. **Integration tests** with test containers (Podman)
3. **End-to-end cascade tests** with mock crypto transactions
4. **Performance tests** targeting <100ms retrieval

### Deployment Checklist

- [ ] Deploy Redis Lua scripts
- [ ] Run Alembic migrations for PostgreSQL
- [ ] Initialize Neo4j graph schema
- [ ] Create Qdrant collections
- [ ] Configure RabbitMQ exchanges/queues
- [ ] Deploy Dramatiq workers
- [ ] Set up Kubernetes manifests
- [ ] Configure Prometheus metrics
- [ ] Validate AutoGen agent configs

## Architectural Rationale

### Why This Architecture?

1. **Leverages Existing Stack**: Uses all locked-in components (Dramatiq, RabbitMQ, Redis, etc.) without introducing new dependencies

2. **Incremental Migration**: Can run alongside existing ADR system during transition, with Dramatiq workers processing both old and new formats

3. **Multi-Agent by Design**: AutoGen agents naturally fit the Janus philosophy of distributed cognition

4. **Offline-First**: All components run locally (Podman + Quadlet), with optional cloud scaling via Kubernetes

5. **Durable & Auditable**: PostgreSQL event sourcing + MinIO document storage ensures complete audit trail for regulatory compliance

6. **Performance Optimized**: Redis Lua scripts provide atomic operations without distributed locks, while Qdrant + Neo4j hybrid search maintains <100ms response times

7. **Self-Evolving**: Concept drift detection and taxonomy evolution run as background Dramatiq tasks, continuously improving classification

8. **Blockchain-Ready**: Architecture supports future BDR (Blockchain Decision Records) integration when needed for crypto transactions

This design transforms your ADR system from a static documentation repository into an active, intelligent decision-making platform that aligns perfectly with Janus's vision of a scalable, offline-first personal intelligence architecture.
