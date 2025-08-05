# ADR 0015 – Redis 7 as in-memory cache and transient pub/sub.

| Status | Accepted |
|--------|----------|
| Date   | 2025-08-04 |

## Context
Redis 7 selected as the in-memory key–value store for transient data, caching, pub/sub, and Dramatiq result backend. Evaluated against alternatives; see [evidence](../reference/Janus Backend Architecture – Onboarding Brief.pdf).

## Decision
**Redis 7 chosen for in-memory caching, transient state, pub/sub, and task rate limiting.**

## Consequences
* Clear separation of ephemeral vs durable workloads (Redis vs PostgreSQL/RabbitMQ).
* Supports low-latency caching, global task rate limiting, and Dramatiq results backend.
* Reduces load on durable stores by handling short-lived state in memory.
* Changing this choice requires a superseding ADR.
