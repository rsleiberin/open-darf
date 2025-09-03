# Text2NKG — Real Gold Baseline (deduped per-run receipts)

- Timestamp: 2025-09-02T16:29:56
- Commit: `e693ac82c5e5`
- Receipts root: `var/receipts/phase7a/text2nkg_real/20250902-162728`
- Checkpoint: `/home/tank/.cache/huggingface/hub/models--d4data--biomedical-ner-all/snapshots/015a4050c9ac99722e61c547aa9b4282bcbedc7f`
- Adapter: heuristic fallback in current run (HF optional)

## Split Metrics

| dataset | split | adapter | P | R | F1 |
|---|---|---|---:|---:|---:|
| biored | dev | HeuristicAdapter | 0.000 | 0.000 | 0.000 |
| biored | test | HeuristicAdapter | 0.000 | 0.000 | 0.000 |
| scierc | dev | HeuristicAdapter | 0.000 | 0.000 | 0.000 |
| scierc | test | HeuristicAdapter | 0.000 | 0.000 | 0.000 |

> Note: Baseline uses deterministic heuristic adapter → values near zero expected until a trained NER head is wired.

## Provenance
- `hf_config.json`, `manifest.json`, and per-run `{dataset}_{split}/metrics.json` are stored under the receipts root.
- Each per-run dir includes `audit.jsonl` + `audit_summary.json` (tri-state receipts).