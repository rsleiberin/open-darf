#!/usr/bin/env bash
set -Ee -o pipefail; set +u
ROOT="${1:-var/receipts/phase6b/*/receipts/_last}"
LAST="$(ls -1d $ROOT 2>/dev/null | sort | tail -n1 || true)"
test -n "$LAST" || { echo "❌ no receipts path found: $ROOT"; exit 1; }

SC="$LAST/scierc_scores_ml_test.json"
BI="$LAST/biored_scores_ml_test.json"

scripts/validate_accuracy_receipts.sh "$LAST"

jq -e '(.micro.F1 // 0) >= 0.50' "$SC" >/dev/null || { echo "❌ SciERC F1 < 0.50"; exit 1; }
jq -e '(.micro.F1 // 0) >= 0.75' "$BI" >/dev/null || { echo "❌ BioRED F1 < 0.75"; exit 1; }

echo "✅ Accuracy gates passed @ $LAST"
