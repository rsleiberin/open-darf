# Relation Demo (Phase-6C)

This demo emits **receipt-driven** relation metrics without any network dependencies.

## Quick start

~~~bash
make rel-demo
~~~

This writes:

- `var/receipts/phase6c/validation/toy_biored.jsonl` (tiny toy)
- `var/receipts/phase6c/validation/biored_relations_scores_heuristic.json`

and prints the `biored` metrics (expected F1 = 1.0 for the toy).

## Run manually

~~~bash
PYTHONPATH=$PWD python3 -m scripts.relation_extraction.emit_rel_metrics \
  --input var/receipts/phase6c/validation/toy_biored.jsonl \
  --out var/receipts/phase6c/validation/biored_relations_scores_heuristic.json \
  --predictor heuristic
~~~

**Note:** Relations remain *non-gated* in CI during Phase-6C; this is a developer tool and receipt generator only.
