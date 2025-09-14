#!/usr/bin/env bash
set -euo pipefail

COUNT="${1:-6}"
ROOT="${PWD}"
BASE="var/receipts"

echo "[peek] base: $BASE  (show latest $COUNT dirs by mtime)"
if [ ! -d "$BASE" ]; then
  echo "[peek] no receipts directory yet."
  exit 0
fi

# Collect directories sorted by modification time (ascending), then take last COUNT
# format: "epoch path" → sort -n → awk path
mapfile -t DIRS < <(find "$BASE" -mindepth 1 -maxdepth 1 -type d -printf "%T@ %p\n" \
  2>/dev/null | sort -n | awk '{ $1=""; sub(/^ /,""); print }')

TOTAL="${#DIRS[@]}"
if [ "$TOTAL" -eq 0 ]; then
  echo "[peek] no subdirectories under $BASE."
  exit 0
fi

START=$(( TOTAL > COUNT ? TOTAL-COUNT : 0 ))

echo "=== Latest receipts (up to $COUNT) ==="
for (( i=START; i<TOTAL; i++ )); do
  d="${DIRS[$i]}"
  printf "%3d. %s  (mtime: " "$((i+1))" "$d"
  date -r "$d" "+%Y-%m-%d %H:%M:%S" 2>/dev/null || echo -n "n/a"
  echo ")"
done

LATEST="${DIRS[$((TOTAL-1))]}"
echo "=== Latest dir: $LATEST ==="
if [ -d "$LATEST" ]; then
  echo "--- files in latest ---"
  ls -lah "$LATEST" || true
  echo "--- tails (first 200 lines each) ---"
  shopt -s nullglob
  for f in "$LATEST"/*.log "$LATEST"/*.out "$LATEST"/*.rc; do
    echo "----- begin: $(basename "$f") -----"
    sed -n '1,200p' "$f" || true
    echo "----- end: $(basename "$f") -----"
  done
  shopt -u nullglob
fi

# Also surface the most recent umbrella and gpu diag logs across all receipts
LATEST_UMBRELLA="$(find "$BASE" -type f -name 'install.verbose.log' 2>/dev/null | sort | tail -n 1 || true)"
LATEST_GPU="$(find "$BASE" -type f -name 'gpu_diag.verbose.log' 2>/dev/null | sort | tail -n 1 || true)"

if [ -n "${LATEST_UMBRELLA:-}" ] && [ -f "$LATEST_UMBRELLA" ]; then
  echo "=== Most recent umbrella log: $LATEST_UMBRELLA (head 200) ==="
  sed -n '1,200p' "$LATEST_UMBRELLA" || true
fi
if [ -n "${LATEST_GPU:-}" ] && [ -f "$LATEST_GPU" ]; then
  echo "=== Most recent GPU diag log: $LATEST_GPU (head 200) ==="
  sed -n '1,200p' "$LATEST_GPU" || true
fi

echo "[peek] done."
