#!/usr/bin/env bash
# Non-fatal v0.1.0 receipt validator
# - Preserves key order using jq keys_unsorted
# - Never exits non-zero (prints PASS/FAIL for humans and CI logs)
set -o pipefail

RECEIPT="${1:-}"
RECEIPT_DIR="open-darf/var/receipts/open-darf"
EXPECTED='["receipt_version","receipt_id","timestamp","iterations","system_context","performance_percentiles","value_metrics","validation_results","comparative_analysis","methodology","evidence_artifacts"]'

echo "=== v0.1.0 Receipt Validator (non-fatal) ==="

# Resolve receipt path
if [ -z "$RECEIPT" ]; then
  RECEIPT="$(ls -t "$RECEIPT_DIR"/validation_*.json 2>/dev/null | head -1 || true)"
fi

if [ -z "$RECEIPT" ] || [ ! -f "$RECEIPT" ]; then
  echo "[error] No receipt found. Provide a path or ensure $RECEIPT_DIR contains validation_*.json"
  exit 0
fi
echo "[file] $RECEIPT"

# Check jq
if ! command -v jq >/dev/null 2>&1; then
  echo "[error] jq not found on PATH"
  exit 0
fi

# Schema evaluation (order-aware)
ACTUAL="$(jq -c 'keys_unsorted' "$RECEIPT" 2>/dev/null || echo '[]')"
COUNT="$(echo "$ACTUAL" | jq 'length')"
ORDER_OK="$(jq -cn --argjson exp "$EXPECTED" --argjson act "$ACTUAL" '$exp == $act')"
MISSING="$(jq -cn --argjson exp "$EXPECTED" --argjson act "$ACTUAL" '$exp - $act')"
UNEXPECTED="$(jq -cn --argjson exp "$EXPECTED" --argjson act "$ACTUAL" '$act - $exp')"

VER="$(jq -r '.receipt_version // "unknown"' "$RECEIPT")"
ITERS="$(jq -r '.iterations // "unknown"' "$RECEIPT")"

echo "[keys.count] $COUNT"
echo "[keys.order_preserved] $ORDER_OK"
echo "[keys.actual_unsorted] $ACTUAL"
echo "[keys.expected]        $EXPECTED"
echo "[field.receipt_version] $VER"
echo "[field.iterations]      $ITERS"
echo "[diff.missing]          $MISSING"
echo "[diff.unexpected]       $UNEXPECTED"

# Numeric sanity (does not fail)
jq -e '
  .performance_percentiles.end_to_end_latency_ms.p50     as $p50   |
  .performance_percentiles.end_to_end_latency_ms.p90     as $p90   |
  .performance_percentiles.end_to_end_latency_ms.p95     as $p95   |
  .performance_percentiles.end_to_end_latency_ms.p99     as $p99   |
  .performance_percentiles.component_timing_ms.document_ingestion.p50 as $doc |
  .performance_percentiles.component_timing_ms.rule_retrieval.p50     as $rule |
  .performance_percentiles.component_timing_ms.audit_write.p50        as $audit |
  ([$p50,$p90,$p95,$p99,$doc,$rule,$audit] | all(type=="number"))
' "$RECEIPT" >/dev/null 2>&1 && echo "[sanity.numeric] OK" || echo "[sanity.numeric] WARN"

if [ "$ORDER_OK" = "true" ] && [ "$COUNT" -eq 11 ] && [ "$VER" = "0.1.0" ]; then
  echo "[PASS] Canonical v0.1.0 receipt."
else
  echo "[FAIL] Non-canonical or legacy schema (see details above)."
fi

echo "[done] Non-fatal validation complete."
