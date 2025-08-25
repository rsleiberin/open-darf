# Phase-2 Reviewer Guide (DARF) — 20250825-025653

## What landed in this PR
- #240 — DENY precedence wired via env-gated graph adapter (preserves logging contract).
- #241 — Tri-state decisions (ALLOW / DENY / INDETERMINATE) propagation validated.
- #242 — Fail-closed enforced in production (adapter entry clamp + guard utilities + tests).
- #243 — Minimal scope taxonomy + evaluator, with perf receipt and audit traces.

## Receipts (append-only)
- Baseline perf: `docs/audit/performance/baseline/20250825-013137`
- Engine precedence hot-path: `docs/audit/performance/engine_precedence/20250825-020407`
- Tri-state distribution (normal + degraded): `docs/audit/validation/tristate_distribution/20250825-020326`
- Fail-closed scenario (Neo4j outage): `docs/audit/security/fail_closed/20250825-015909`
- Scope evaluator perf: `docs/audit/performance/scope_eval/20250825-020543`
- Scope decision audit (principal/action/resource): `docs/audit/authorization/scope_decisions/20250825-020709`

## Safepoint
- Latest tag: `safepoint-20250825-024657`

## How to verify locally (safe subset)
```bash
darf-env
git switch feat/phase2-deny-precedence-20250825-013137
pytest -q tests -k 'not postgres_connection and not neo4j' -s -vv
```

### Env flags
- Graph precedence is behind `CONSTITUTION_USE_GRAPH_PRECEDENCE=1`.
- Production fail-open is clamped off at adapter entry; `ENGINE_FAIL_OPEN` is ignored in prod.

### Enable graph precedence locally

Export the env flag and run the tests; no live DB required:

    export GRAPH_PRECEDENCE=1
    pytest -q tests/constitution_graph/test_precedence_adapter.py
    pytest -q tests/api/test_validation_dto_and_logging.py
