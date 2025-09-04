# Scored Evaluation Runner

This runner wires **mapping → validation → metrics** and writes receipts.

## Modes

1. **Smoke mode** (no heavy downloads)
   - Generates tiny synthetic predictions/gold.
   - If no `label_map` is provided, it defaults to mapping `HEUR → ENT`.

    python tools/text2nkg/run_eval_scored.py \
      --dataset biored --split dev \
      --outdir var/receipts/phase7b/smoke_$(date +%Y%m%d-%H%M%S) \
      --smoke --write-docs-scoreboard

2. **Path-based mode** (real predictions & gold)
   - Provide `--pred-path` and `--gold-path` pointing to JSON/JSONL files.
   - Accepted formats:
     - Object with spans: `{ "spans": [ {...}, ... ] }`
     - Array of spans: `[ {...}, ... ]`
     - JSON Lines: one span per line

    python tools/text2nkg/run_eval_scored.py \
      --dataset biored --split dev \
      --outdir var/receipts/phase7b/dev_$(date +%Y%m%d-%H%M%S) \
      --pred-path path/to/pred.jsonl \
      --gold-path path/to/gold.json \
      --config configs/hf_config.json \
      --write-docs-scoreboard

## Outputs

- `pred_spans.jsonl` — normalized valid spans.
- `metrics.json` — includes `strict`, `unlabeled_boundary`, `unlabeled_text_multiset`, `adapter`, and `skipped_invalid_pred_spans`.
- `scoreboard.json` — compact summary. A timestamped copy is also written to `docs/scoreboards/` when `--write-docs-scoreboard` is used.

## Controls

- Set `DARF_BYPASS_MAP=1` to disable mapping (diagnostics/rollback). Shapes remain normalized so downstream steps still work.

## Notes

- Keep heavy artifacts under `var/` (already gitignored).
- Avoid adapter-level mapping; use the pipeline transform only.
