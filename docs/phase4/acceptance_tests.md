# Phase-4 Acceptance Tests (outline)

1) Extractor determinism
   - Input: fixed seed text.
   - Expect: stable set of Entity(name, etype) with spans.

2) Guard enforcement
   - Given check returns DENY → writes rejected with PermissionError.
   - Given check returns ALLOW → writes succeed.

3) Hyperedge integrity
   - Participants must reference existing Entity.uids.
   - Roles non-empty strings; duplicate (role, entity) pairs rejected at client layer.

4) Storage bootstrap
   - Neo4j constraints/indexes applied successfully.
   - Qdrant 'facts' collection exists with configured dims.

5) Perf sanity (dev)
   - Extractor p95 < 50 ms on ~3 KB text.
   - Qdrant search p95 < 50 ms for d∈{64,384} top-10.

## Running Phase-4 acceptance

Scenarios live in `tests/acceptance/test_phase4_acceptance.py` and validate tri-state scope decisions (ALLOW/DENY/INDETERMINATE),
guard-call behavior, and scope-guarded writes with audit. Run:

```bash
pytest -q tests/acceptance
```

Perf suites are **opt-in** via `RUN_PERF=1` and **do not** require services.
