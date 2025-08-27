# Phase 5 — Operational ML Enablement (Status)

- ✅ Group 1: Environment & repo baseline
- ✅ Group 2: SciBERT extractor scaffold (flag-gated)
- ✅ Group 3: BioBERT extractor scaffold (flag-gated)
- ✅ Group 4: Text2NKG n-ary relations (hyperedges)
- ✅ Group 5: Temporal model scaffold (timespan extraction)
- ✅ Group 6: Constitutional middleware (pre/post; DENY precedence)
- ✅ Group 7: Perf hooks & QA (RUN_PERF gating)
- ✅ Group 8: Docs & issues (this doc)
- ✅ Group 9: Risks & rollback hardening

## How to run locally

1) `source var/local/testing.env`
2) Try stubs:
   - `python3 tools/try_text2nkg.py "Vitamin C prevents scurvy."`
   - `python3 tools/try_temporal.py "System migrated from 2017 to 2019"`
3) Enable flags (example):
   - `export EXTRACTOR_TEXT2NKG=1` · `export TEMPORAL_GRAPH_MODEL=1`
4) Perf smoke (optional):
   - `RUN_PERF=1 python3 tools/perf/run_perf.py`
