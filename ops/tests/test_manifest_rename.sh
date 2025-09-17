#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
TD="$ROOT/var/tests/ingest_$(date +%s)"
mkdir -p "$TD"
echo "file A $(date -Is)" > "$TD/a.txt"
printf 'B\n' > "$TD/b.txt"

m1="$(ops/bin/ingest_path.sh "$TD" | tail -n1)"

# Simulate rename of a.txt -> a_renamed.txt and add c.txt
mv "$TD/a.txt" "$TD/a_renamed.txt"
printf 'C\n' > "$TD/c.txt"

m2="$(ops/bin/ingest_path.sh "$TD" | tail -n1)"

out="$(ops/bin/compare_manifests.sh "$m1" "$m2")"
echo "$out"

# Expect adds:1 dels:0 renames:1 unchanged:1
adds="$(sed -n 's/.*adds:\([0-9]\+\).*/\1/p' <<< "$out")"
dels="$(sed -n 's/.*dels:\([0-9]\+\).*/\1/p' <<< "$out")"
rens="$(sed -n 's/.*renames:\([0-9]\+\).*/\1/p' <<< "$out")"
unch="$(sed -n 's/.*unchanged:\([0-9]\+\).*/\1/p' <<< "$out")"

if [[ "$adds" == "1" && "$dels" == "0" && "$rens" == "1" && "$unch" == "1" ]]; then
  echo "[TEST] manifest_rename: PASS"
  exit 0
else
  echo "[TEST] manifest_rename: FAIL (adds=$adds dels=$dels renames=$rens unchanged=$unch)"
  exit 1
fi
