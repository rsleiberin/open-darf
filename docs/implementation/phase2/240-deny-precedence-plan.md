# #240 — DENY Precedence Integration (Implementation Plan)

## Objective
Integrate DENY precedence into the constitutional validation hot-path, exposing `allow_exists` and `deny_exists` from Neo4j queries and resolving via `decide_precedence` with clear `reason_code` propagation.

## Tasks
- [x] Graph query contract: return `allow_exists`, `deny_exists` (fast path, bounded traversal).
- [ ] Engine: integrate `decide_precedence(allow_exists, deny_exists)` → `ALLOW|DENY|INDETERMINATE`.
- [ ] Reason codes: include first decisive reason; preserve logging contract `decision=<X> reason=<Y>`.
- [ ] Tests:
  - [ ] Unit: mixed allow/deny, deny-only, allow-only, none-present.
  - [ ] Degraded paths: db timeout/error → `INDETERMINATE` (see #242).
- [x] Performance receipt: baseline smoke captured (log + JSON). p95 targets to be measured after wiring.

## Receipts
- Append-only under `docs/audit/performance/` and `docs/audit/validation/`.
- Include sample counts, p50/p95/max, run timestamp, and flags (e.g., `neo4j_enabled`).

## Risks
- Query fan-out → guard with bounds; ensure indexes are present.
- Logging volume → single-line decision logs only.

## Definition of Done
- End-to-end precedence verified, receipts added, CI Class-A green, PR labels compliant.
