# Phase 7B Acceptance

To verify that a path-based run matches the **golden** strict F1 within tolerance (±0.002), run:

    # Produce dev/test scoreboards (path-based example)
    python tools/text2nkg/run_eval_scored.py \
      --dataset biored --split dev \
      --outdir var/receipts/phase7b/biored_dev_$(date +%Y%m%d-%H%M%S) \
      --pred-path path/to/pred_dev.jsonl \
      --gold-path path/to/gold_dev.jsonl \
      --config configs/hf_config.json \
      --write-docs-scoreboard

    python tools/text2nkg/run_eval_scored.py \
      --dataset biored --split test \
      --outdir var/receipts/phase7b/biored_test_$(date +%Y%m%d-%H%M%S) \
      --pred-path path/to/pred_test.jsonl \
      --gold-path path/to/gold_test.jsonl \
      --config configs/hf_config.json \
      --write-docs-scoreboard

Then check against the golden:

    python tools/text2nkg/check_golden.py \
      --dev-scoreboard var/receipts/phase7b/biored_dev_*/scoreboard.json \
      --test-scoreboard var/receipts/phase7b/biored_test_*/scoreboard.json \
      --golden docs/scoreboards/biored_phase7a_20250903-172808.json \
      --tol 0.002

Exit code **0** = pass; **3** = fail. The script prints a JSON report with deltas.
