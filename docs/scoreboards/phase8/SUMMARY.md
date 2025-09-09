# Phase 8 Scoreboard — 2025-09-09 04:57:39Z

Receipts-driven leaderboard compiled from `re_eval_metrics.json` found under:
- `var/receipts/phase7h/full_suite/*/*` (identity/plumbing)
- `var/receipts/phase8/**` (real baselines: PURE / PL-Marker / heuristic)

| dataset | model | split | precision | recall | f1 | comp | preds | gold | latency_ms | receipt |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| biored_norm | toy-identity-eval | dev | 1.0 | 1.0 | 1.0 | 1.0 | 9168 | 9168 | 0.0 | var/receipts/phase7h/full_suite/biored_norm/20250909-025550/re_eval_metrics.json |
| biored_official | toy-identity-eval | dev | 1.0 | 1.0 | 1.0 | 1.0 | 16712 | 16712 | 0.0 | var/receipts/phase7h/full_suite/biored_official/20250909-025551/re_eval_metrics.json |
| scierc | toy-identity-eval | dev | 1.0 | 1.0 | 1.0 | 1.0 | 0 | 0 | 0.0 | var/receipts/phase7h/full_suite/scierc/20250909-025552/re_eval_metrics.json |
| scierc_json | toy-identity-eval | dev | 1.0 | 1.0 | 1.0 | 1.0 | 4615 | 4615 | 0.0 | var/receipts/phase7h/full_suite/scierc_json/20250909-025552/re_eval_metrics.json |
| scierc_norm | toy-identity-eval | dev | 1.0 | 1.0 | 1.0 | 1.0 | 4615 | 4615 | 0.0 | var/receipts/phase7h/full_suite/scierc_norm/20250909-025550/re_eval_metrics.json |

## Targets (must meet before any open-source packaging)
- **SciERC**: F1_micro ≥ 0.50 (PURE / PL-Marker)
- **BioRED**: entity ≥ 0.90, relation ≥ 0.65

## Notes
- Phase 7H identity-eval rows will show F1=1.0; these validate plumbing, not model accuracy.
- Phase 8 model rows (PURE / PL-Marker / heuristic) will determine acceptance vs targets.