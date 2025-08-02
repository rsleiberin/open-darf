#!/usr/bin/env bash
# Aggregate validation evidence and generate statistics
set -euo pipefail

EVIDENCE_DIR="evidence/validation_receipts"
OUTPUT_FILE="evidence/aggregated_metrics.json"

if [ ! -d "$EVIDENCE_DIR" ]; then
    echo "No evidence directory found: $EVIDENCE_DIR"
    exit 1
fi

RECEIPT_COUNT=$(find "$EVIDENCE_DIR" -name "validation_*.json" -type f | wc -l)
if [ "$RECEIPT_COUNT" -eq 0 ]; then
    echo "No validation receipts found in $EVIDENCE_DIR"
    exit 1
fi

echo "Aggregating $RECEIPT_COUNT validation receipts..."

# Use jq to aggregate metrics
jq -s '
{
  aggregation_timestamp: (now | strftime("%Y-%m-%dT%H:%M:%SZ")),
  total_validations: length,
  platforms: (group_by(.system_context.platform) | map({platform: .[0].system_context.platform, count: length})),
  performance_stats: {
    avg_total_ms: (map(.pipeline_performance.total_end_to_end_ms) | add / length | round),
    min_total_ms: (map(.pipeline_performance.total_end_to_end_ms) | min),
    max_total_ms: (map(.pipeline_performance.total_end_to_end_ms) | max),
    avg_db_percentage: (map(.pipeline_performance.percentage_breakdown.database_io) | add / length | . * 100 | round / 100),
    avg_decision_logic_percentage: (map(.pipeline_performance.percentage_breakdown.decision_logic) | add / length | . * 100 | round / 100)
  },
  validation_results: {
    total_constitutional_checks: (map(.constitutional_validations | length) | add),
    accept_decisions: (map(.constitutional_validations | map(select(.decision == "ACCEPT")) | length) | add),
    deny_decisions: (map(.constitutional_validations | map(select(.decision == "DENY")) | length) | add)
  },
  system_health: {
    neo4j_accessible: (map(.system_verification.neo4j_rules_loaded) | all),
    postgres_accessible: (map(.system_verification.postgres_audit_working) | all),
    content_addressing_working: (map(.system_verification.content_addressing_verified) | all)
  }
}
' "$EVIDENCE_DIR"/validation_*.json > "$OUTPUT_FILE"

echo "Aggregated metrics written to: $OUTPUT_FILE"
cat "$OUTPUT_FILE"
