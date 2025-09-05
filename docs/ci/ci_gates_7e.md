# CI Gates (7E) — Validation Inputs & Gates

Required inputs tracked in repo:
- var/receipts/phase6c/validation/scierc_scores_ml_test.json (keys: micro.P, micro.R, micro.F1)
- var/receipts/phase6c/validation/biored_scores_ml_test.json (keys: micro.entity_f1, micro.relation_f1)

Metrics rebuild step writes: var/receipts/phase6c/validation/metrics.json  
Emitter writes: var/reports/phase6c/gates.json  
Verifier: scripts/ci_verify_gates.py (ensures presence and non-regression).

Local quickrun:
    python scripts/emit_perf_and_constitution.py --eval var/receipts/phase6c/validation --out var/reports/phase6c/gates.json
    python scripts/ci_verify_gates.py
    python scripts/print_scoreboard.py

Notes:
- Do not remove Phase 6C receipts during 7E work; CI Gates depends on them.
- .gitignore allowlist rules keep only the minimal validation inputs tracked.
