# Phase 7F — Orchestrator (A2, Parallel)
- Runs vector (Qdrant stub/real) and graph (Neo4j stub/real) in parallel.
- Fuses with RRF(k=60); applies deny-precedence; fail-closed on constraint errors.
- Writes receipt under `var/receipts/phase7f/orchestrator_parallel/<ts>/summary.json`.

Example (stubbed):
scripts/phase7f/synthesis_orchestrator_parallel.py --constraints var/receipts/phase7f/orchestrator_run/constraints_demo.json
