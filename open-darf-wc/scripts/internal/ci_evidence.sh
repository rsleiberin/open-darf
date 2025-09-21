#!/usr/bin/env bash
set -euo pipefail
printf "===\n===\n===\n"
echo "=== Open-DARF · CI Evidence Publisher (Linux) ==="
ROOT="$(cd "$(dirname "$0")/.."; pwd)"
RESULTS="$ROOT/results"
PUB="$RESULTS/publish"; mkdir -p "$PUB"

latest="$(ls -1t "$RESULTS"/evidence_*.* 2>/dev/null | head -n1 || true)"
if [ -z "$latest" ]; then echo "[!] No evidence archives found in $RESULTS"; exit 2; fi

fname="$(basename "$latest")"
dest="$PUB/$fname"
cp -f "$latest" "$dest"

sha=""; if command -v sha256sum >/dev/null 2>&1; then sha="$(sha256sum "$dest" | awk '{print $1}')"; fi
size="$(stat -c%s "$dest" 2>/dev/null || stat -f%z "$dest")"
host="$(hostname)"
ts="$(date -Is)"

cat > "$PUB/evidence_manifest.json" <<MAN
{
  "ts": "$ts",
  "host": "$host",
  "file": "$fname",
  "size_bytes": $size,
  "sha256": "$sha"
}
MAN
echo "[✓] Published: $dest"
echo "[✓] Manifest : $PUB/evidence_manifest.json"
