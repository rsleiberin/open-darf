#!/usr/bin/env bash
set -euo pipefail
# Usage: validator_benchmark.sh <file> [runs]
f="$1"; runs="${2:-30}"
declare -a lat
declare -i i=0

# Warmup
ops/bin/tri_state_validator.sh "$f" >/dev/null

# Collect latencies from receipts
while (( i < runs )); do
  rec_line="$( (ops/bin/tri_state_validator.sh "$f" 2>&1) | sed -n 's/^\[validator\] wrote: //p' | tail -n1 )"
  [[ -f "$rec_line" ]] || continue
  l="$(sed -n 's/.*"latency_ms":\([0-9][0-9]*\).*/\1/p' "$rec_line")"
  lat+=("$l")
  i+=1
done

# Compute p95
printf '%s\n' "${lat[@]}" | sort -n > /tmp/lat.$$ 2>/dev/null || true
n="$(wc -l < /tmp/lat.$$ | tr -d ' ')"
idx=$(( (95*n + 99)/100 ))  # ceil(0.95*n)
(( idx < 1 )) && idx=1
p95="$(sed -n "${idx}p" /tmp/lat.$$)"
p50="$(sed -n "$(( (n+1)/2 ))p" /tmp/lat.$$)"
p99="$(sed -n "$(( (99*n + 99)/100 ))p" /tmp/lat.$$)"

out="docs/evidence/constitution/benchmark_$(basename "$f")_$(date +%s).json"
mkdir -p "$(dirname "$out")"
{
  printf '{'
  printf '"file":"%s",' "$f"
  printf '"runs":%s,' "$n"
  printf '"p50_ms":%s,' "${p50:-0}"
  printf '"p95_ms":%s,' "${p95:-0}"
  printf '"p99_ms":%s' "${p99:-0}"
  printf '}'
} > "$out"

echo "[benchmark] wrote: $out"
