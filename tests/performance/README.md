# Performance Tests (CI-Skipped)

- These tests run **only** when `RUN_PERF=1` is set.
- They validate that recent receipts exist and include expected fields.
- Use the helper:
  ~~~bash
  RUN_PERF=1 tools/perf/run_phase6_perf.sh
  ~~~
