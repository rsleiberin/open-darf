# ML Local Quickstart

This guide helps you run Phase-6 validation locally without CI.

## Prereqs
- Python 3.10+
- `pip install -r requirements.txt`
- (Optional) `pre-commit install` if you plan to commit

## Core flags
- `EXTRACTOR_SCI=1` – enable SciERC
- `EXTRACTOR_BIO=1` – enable BioRED
- `EXTRACTOR_TEXT2NKG=1` – enable the lightweight relation extractor
- `TEMPORAL_GRAPH_MODEL=1` – enable temporal parsing
- `RUN_PERF=1` – record perf timers locally (defaults OFF in CI)
- `OBS_ENABLE=1` – write JSONL counters/timers to `var/metrics/` (defaults OFF)

> Tip: Keep `RUN_PERF=1` and `OBS_ENABLE=1` **off** during normal unit tests. Turn them on only when explicitly measuring locally.

## Quick validity checks
    # Temporal parser smoke
    python -c 'from apps.knowledge_graph.temporal_model import parse_timespan as p; print(p("2021-03-15"))'

    # Relation extractor smoke
    python -c "from apps.extractors.text2nkg_extractor import extract_relations_simple as x; print(x('Aspirin treats fever'))"
