# Audit Receipts (append-only)

Untracked, local-only by default (see `.git/info/exclude`):
- infra/, hyperrag_perf/, guard_perf/, guard_probe/, qdrant_perf/, neo4j_info/, storage_bootstrap/, perf_sanity/

Tracked `_last/` mirrors (restore to HEAD before committing):
- pipeline_cbdt/_last/, pipeline_oscar/_last/, pipeline_prov/_last/

Restore helper:
    tools/restore_last.sh

Exclude helper:
    tools/receipts_exclude.sh
