#!/usr/bin/env bash
set -Eeuo pipefail
cd "$(git rev-parse --show-toplevel)"
EX=".git/info/exclude"
touch "$EX"
while read -r p; do
  grep -qxF "$p" "$EX" 2>/dev/null || echo "$p" >> "$EX"
done <<'LIST'
docs/audit/infra/
docs/audit/hyperrag_perf/
docs/audit/guard_perf/
docs/audit/guard_probe/
docs/audit/qdrant_perf/
docs/audit/neo4j_info/
docs/audit/storage_bootstrap/
docs/audit/perf_sanity/
LIST
echo "Updated .git/info/exclude with receipt paths."
