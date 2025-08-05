# ADR 0016 – LangChain + AutoGen + GraphRAG for RAG orchestration.

| Status | Accepted |
|--------|----------|
| Date   | 2025-08-04 |

## Context
LangChain, AutoGen, and GraphRAG locked in as the AI orchestration layer for multi-agent reasoning, hybrid retrieval (vector + graph), and tool integration. Evaluated against alternatives; see [evidence](../reference/Janus Backend Architecture – Onboarding Brief.pdf).

## Decision
**LangChain + AutoGen + GraphRAG selected as the orchestration framework for agent reasoning, multi-agent workflows, and retrieval-augmented generation.**

## Consequences
* Enables hybrid retrieval from Qdrant and Neo4j within the same reasoning cycle.
* Supports multi-agent collaboration patterns via AutoGen.
* Standardizes tool integration, retrieval, and prompt management for all agents.
* Changing this choice requires a superseding ADR.
