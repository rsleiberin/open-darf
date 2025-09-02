#!/usr/bin/env bash
set -euo pipefail
ROOT="${1:-var/receipts/phase7a/text2nkg}"
THRESH_US=1000.0
fails=0
for p in $(ls -1 ${ROOT}/*/audit_summary.json 2>/dev/null || true); do
  p95=$(python3 -c "import json,sys;print(json.load(open(sys.argv[1])).get('p95_us', 1e9))" "$p")
  awk_res=$(awk -v v="$p95" -v t="$THRESH_US" 'BEGIN{if (v<t) print "PASS"; else print "FAIL"}')
  echo "check: $p  p95_us=$p95  => $awk_res"
  [ "$awk_res" = "PASS" ] || fails=$((fails+1))
done
if [ "$fails" -gt 0 ]; then
  echo "❌ CI preflight failed: $fails run(s) exceed p95 threshold ${THRESH_US}us"
  exit 1
fi
echo "✓ CI preflight passed: all runs p95 < ${THRESH_US}us"
