# TODO — Evaluators (PURE / PL-Marker Integration)

- [ ] GPU runner scripts with receipts:
      - `apps/relex/pure/runner.py` → writes `re_eval_metrics.json` (metrics_v1)
      - `apps/relex/plmarker/runner.py` → same schema
- [ ] CI opt-in labels: `ci:run-pure`, `ci:run-plmarker` (fail-closed on schema)
- [ ] Scoreboard builder to aggregate receipts → `docs/scoreboards/phase8/SUMMARY.md`
