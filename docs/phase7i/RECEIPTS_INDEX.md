# Phase 7I — Receipts Index

Receipts live under `var/receipts/phase7i/<model>/<timestamp>/`.
Each run includes:
- `env.json` — environment & service snapshot
- `inputs.json` — dataset & config pointers
- `metrics.json` — schema: `docs/schemas/metrics_v1.json`
- `scoreboard.json` — compact row for aggregation
- `decision.json` — accept/indeterminate with rationale
