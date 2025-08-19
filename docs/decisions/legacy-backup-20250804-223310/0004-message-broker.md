# ADR 0004 – RabbitMQ 3 adopted as default message broker.

| Status | Accepted |
|--------|----------|
| Date   | 2025-08-03 |

## Context
RabbitMQ 3 adopted as default message broker. was evaluated against alternatives; see [evidence](../reference/Redis vs RabbitMQ as Dramatiq Brokers – A Durable Self-Hosted Task Queue Comparison.pdf).

## Decision
**RabbitMQ 3 adopted as default message broker.**

## Consequences
* Establishes a stable contract for related components.
* Changing this choice requires a superseding ADR.
