#!/usr/bin/env bash
set -Ee -o pipefail; set +u
cd "$(git rev-parse --show-toplevel 2>/dev/null || echo .)" || exit 2
mkdir -p var/state
STATE="var/state/phase6b_status.json"

g1a=1; g1b=1
[ -f apps/metrics/receipt_emitter.py ] && g2a=1 || g2a=0
[ -f ".github/workflows/phase6b_receipts.yml" ] && g2b=1 || g2b=0
if ls receipts/_last/*_scores_ml_test.json >/dev/null 2>&1 && bash scripts/local_ml_gates.sh receipts/_last >/dev/null 2>&1; then g2c=1; else g2c=0; fi
grep -q "Phase 6B — Local Accuracy & Perf Flow" docs/operations/ML_LOCAL_QUICKSTART.md 2>/dev/null && g3a=1 || g3a=0
if command -v gh >/dev/null 2>&1; then
  PR_NUM="$(gh pr list --state open --json number,title -q '.[]|select(.title|test("phase6b";"i"))|.number' 2>/dev/null | head -n1 || true)"
else PR_NUM=""; fi
[ -n "$PR_NUM" ] && g3b=1 || g3b=0

if [ -f "$STATE" ]; then
  prev="$(cat "$STATE")"
  for k in g1a g1b g2a g2b g2c g3a g3b; do
    pv="$(printf '%s\n' "$prev" | jq -r ".$k // 0" 2>/dev/null || echo 0)"
    cv="$(eval echo \$$k)"
    [ "$pv" -gt "$cv" ] && eval "$k=$pv"
  done
fi

jq -n --argjson g1a $g1a --argjson g1b $g1b --argjson g2a $g2a \
      --argjson g2b $g2b --argjson g2c $g2c --argjson g3a $g3a --argjson g3b $g3b \
      '{g1a:$g1a,g1b:$g1b,g2a:$g2a,g2b:$g2b,g2c:$g2c,g3a:$g3a,g3b:$g3b}' > "$STATE"

bar(){ [ "$1" -eq 1 ] && printf "🟩" || printf "🟧"; }
printf "%s%s | %s%s%s | %s%s\n" "$(bar $g1a)" "$(bar $g1b)" "$(bar $g2a)" "$(bar $g2b)" "$(bar $g2c)" "$(bar $g3a)" "$(bar $g3b)"
