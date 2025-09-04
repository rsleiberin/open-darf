# Label Mapping Transform (Phase 7B)

This document explains how DARF maps model output labels to a canonical set during the **Text→NKG** pipeline. The mapping is a **pure, configurable transform** applied after prediction and before export/metrics.

## Why a pipeline transform?

- Keeps **adapters dumb** and reusable.
- Centralizes governance: a single source of truth for label policy.
- Enables **runtime control** (config + environment) without code changes.

## Where it lives

- Transform: `tools/text2nkg/transforms/label_map.py`
- Validator: `tools/text2nkg/emit_nkg.py: assert_valid_spans`
- Runner: `tools/text2nkg/run_eval_scored.py`

## Configuration

Provide a `label_map` in your JSON config. Keys are matched **exactly** first, then by a **canonical** form (lowercased, non-alphanumeric removed).

    {
      "label_map": {
        "HEUR": "ENT",
        "heur": "ENT"
      }
    }

If a label is not present in the map:

- If `label_map_default` is set, that value is used.
- Otherwise, the **original label** is preserved.

## Bypass (diagnostics / rollback)

Set `DARF_BYPASS_MAP=1` (or `true`, case-insensitive) in the environment to **disable mapping** entirely. The pipeline will still normalize shapes to `{start,end,label}` so downstream components remain stable.

    DARF_BYPASS_MAP=1 python tools/text2nkg/run_eval_scored.py \
      --dataset biored --split dev --outdir var/tmp/dev --smoke

## Shape guarantees

- The transform returns `list[dict]` with keys: `start`, `end`, `label`.
- Bounds from common aliases (`begin/stop/offset_*`) are preserved.
- Invalid bounds are filtered by `assert_valid_spans` in the exporter; skipped counts are logged.

## One-liner (smoke harness)

Use the scored runner to exercise **mapping → validation → metrics** locally without heavy downloads:

    python tools/text2nkg/run_eval_scored.py \
      --dataset biored --split dev \
      --outdir var/receipts/phase7b/smoke_$(date +%Y%m%d-%H%M%S) \
      --smoke --write-docs-scoreboard

Artifacts:
- `metrics.json` with `strict`, `unlabeled_boundary`, `unlabeled_text_multiset`
- `scoreboard.json` in the run directory
- Timestamped copy in `docs/scoreboards/` when `--write-docs-scoreboard` is used

## Pitfalls & tips

- Do **not** reintroduce adapter-level mapping.
- Keep all heavy artifacts under `var/` (ignored).
- Use the bypass env var to compare pre/post-mapping behavior quickly.
