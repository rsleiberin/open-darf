# Implementation Agent — Phase-2 Wiring (Engine)
- Engine wired (precedence, tri-state, fail-closed, scope gate) with tests.
- Next: expose `decision` + `reason_code` via API (#241), add scope indexes (#243), add counters (E11).
Run:
  .venv/bin/python -m pytest -q tests/engine
  .venv/bin/python -m apps.constitution_engine.schema.init --dry-run
updated: 20250822T015858Z
update: 20250822T020036Z
