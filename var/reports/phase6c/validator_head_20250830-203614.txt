#!/usr/bin/env bash
set -Ee -o pipefail; set +u
root="${1:-receipts/_last}"
fail=0
for f in "$root"/{scierc,biored}_scores_ml_test.json; do
  if [ ! -f "$f" ]; then echo "❌ missing $f"; fail=1; continue; fi
  jq -e '
    .micro and .meta and
    (.micro.P|numbers) and (.micro.R|numbers) and (.micro.F1|numbers) and
    (.micro.tp|numbers) and (.micro.fp|numbers) and (.micro.fn|numbers) and
    (.meta.dataset|test("^(SciERC|BioRED)$")) and
    (.meta.split=="test") and
    (.meta.generated_at|type=="string") and
    (.meta.version|type=="string")
  ' "$f" >/dev/null || { echo "❌ schema invalid: $f"; fail=1; }
done
[ $fail -eq 0 ] && echo "✅ receipts schema OK" || exit 1
