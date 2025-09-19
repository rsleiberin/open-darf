# DO NOT COMMIT THIS FILE — PREVIEW OF PROPOSED HEADER
# Header: Purpose
# One or two plain sentences describing what this file does and who runs it.

# Header: Inputs
# - Environment variables / CLI flags
# - External services called (if any)

# Header: Outputs
# - Files/receipts generated
# - Network side effects (ports/endpoints touched)

# Header: Data Flow
# Source → Transform/Validation → Sink (mention receipts directory)

# Header: Failure Modes & Recovery
# Common errors, detection cues, and operator actions.

# Header: Idempotence & Teardown
# What is safe to re-run; cleanup behavior.

# Header: Security & Privacy Notes
# Sensitive ops (if any). Stays local unless explicit user consent for publishing evidence.

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
