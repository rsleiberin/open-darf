#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
TD="$ROOT/var/tests/churn_$(date +%s)"
mkdir -p "$TD"

echo "[churn] Step 1/6: Creating nested test tree (~200 files)…"
levels=(L1 L2 L3 L4)
for l1 in {1..5}; do
  for l2 in {1..5}; do
    for l3 in {1..2}; do
      d="$TD/${levels[0]}$l1/${levels[1]}$l2/${levels[2]}$l3"
      mkdir -p "$d"
      for i in {1..4}; do
        printf "file %s %s %s\n" "$l1-$l2-$l3-$i" "$(date +%s)" "$RANDOM" > "$d/f_$i.txt"
      done
    done
  done
done

echo "[churn] Step 2/6: Ingest initial tree (parallel)…"
t0_ns="$(date +%s%N)"
# Progress appears on STDERR; stdout carries the manifest path only
m1="$(ops/bin/ingest_path.sh "$TD" | tail -n1)"
t1_ns="$(date +%s%N)"

echo "[churn] Step 3/6: Compute manifest root #1…"
r1="$(ops/bin/manifest_root.sh "$m1")"
root1="$(printf '%s' "$r1" | sed -n 's/.*"root":"\([a-f0-9]\{64\}\)".*/\1/p')"
count1="$(printf '%s' "$r1" | sed -n 's/.*"count":\([0-9][0-9]*\).*/\1/p')"
echo "[churn] Root#1: $root1 (count=$count1)"

echo "[churn] Step 4/6: Rename 20 files (no content change)…"
mapfile -t files < <(find "$TD" -type f -name 'f_*.txt' | sort | head -n 20)
for f in "${files[@]}"; do mv "$f" "${f%.txt}_renamed.txt"; done

echo "[churn] Step 5/6: Re-ingest after rename (parallel)…"
m2="$(ops/bin/ingest_path.sh "$TD" | tail -n1)"
r2="$(ops/bin/manifest_root.sh "$m2")"
root2="$(printf '%s' "$r2" | sed -n 's/.*"root":"\([a-f0-9]\{64\}\)".*/\1/p')"
count2="$(printf '%s' "$r2" | sed -n 's/.*"count":\([0-9][0-9]*\).*/\1/p')"
echo "[churn] Root#2: $root2 (count=$count2)"
if [[ "$root1" != "$root2" ]]; then
  echo "[TEST] churn_merkle: FAIL (rename-only changed root)"; exit 1
fi

echo "[churn] Step 6/6: Add 15 + delete 10; re-ingest (parallel)…"
for k in {1..15}; do d="$TD/L1_new/$k"; mkdir -p "$d"; printf "new %s %s\n" "$k" "$(date -Is)" > "$d/new_$k.txt"; done
mapfile -t to_del < <(find "$TD" -type f -name 'f_*.txt' | sort | head -n 10)
for f in "${to_del[@]}"; do rm -f "$f"; done

t2_ns="$(date +%s%N)"
m3="$(ops/bin/ingest_path.sh "$TD" | tail -n1)"
t3_ns="$(date +%s%N)"
r3="$(ops/bin/manifest_root.sh "$m3")"
root3="$(printf '%s' "$r3" | sed -n 's/.*"root":"\([a-f0-9]\{64\}\)".*/\1/p')"
count3="$(printf '%s' "$r3" | sed -n 's/.*"count":\([0-9][0-9]*\).*/\1/p')"
echo "[churn] Root#3: $root3 (count=$count3)"
if [[ "$root3" == "$root1" ]]; then
  echo "[TEST] churn_merkle: FAIL (adds/deletes did not change root)"; exit 1
fi

diffAB="$(ops/bin/compare_manifests.sh "$m1" "$m2")"
diffBC="$(ops/bin/compare_manifests.sh "$m2" "$m3")"

out="docs/evidence/tests/churn_merkle_$(date +%s).json"
mkdir -p "$(dirname "$out")"
{
  printf '{'
  printf '"m1":"%s","m2":"%s","m3":"%s",' "$m1" "$m2" "$m3"
  printf '"root1":"%s","root2":"%s","root3":"%s",' "$root1" "$root2" "$root3"
  printf '"count1":%s,"count2":%s,"count3":%s,' "$count1" "$count2" "$count3"
  printf '"ingest1_ms":%s,' "$(( (t1_ns - t0_ns)/1000000 ))"
  printf '"ingest2_ms":%s,' "$(( (t2_ns - t1_ns)/1000000 ))"
  printf '"ingest3_ms":%s,' "$(( (t3_ns - t2_ns)/1000000 ))"
  printf '"diff_rename":"%s",' "$(echo "$diffAB" | tr -d '"' )"
  printf '"diff_churn":"%s"' "$(echo "$diffBC" | tr -d '"' )"
  printf '}'
} > "$out"

echo "[TEST] churn_merkle: PASS"
echo "[evidence] wrote: $out"
