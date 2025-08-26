#!/usr/bin/env bash
set -Eeuo pipefail
cd "$(git rev-parse --show-toplevel)"
# Only untracked timestamped audit dirs; keep tracked _last/ mirrors
git clean -fd \
  docs/audit/pipeline/pipeline_budget/20* \
  docs/audit/pipeline/pipeline_cbdt/20* \
  docs/audit/pipeline/pipeline_e2e/20* \
  docs/audit/pipeline/pipeline_oscar/20* \
  docs/audit/pipeline/pipeline_perf/20* \
  docs/audit/pipeline/pipeline_prov/20* \
  docs/audit/hyperrag_perf/20* \
  docs/audit/guard_perf/20* \
  docs/audit/guard_probe/20* \
  docs/audit/qdrant_perf/20* \
  docs/audit/neo4j_info/20* \
  docs/audit/storage_bootstrap/20* \
  docs/audit/perf_sanity/20* \
  docs/audit/infra/20* \
  docs/audit/summary/20* || true
echo "Cleaned untracked timestamped audit directories."
