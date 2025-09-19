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
echo "=== Open-DARF · Build Peer Bundle (Linux) ==="
ROOT="$(cd "$(dirname "$0")/.."; pwd)"
OUTDIR="$ROOT/results/bundles"; mkdir -p "$OUTDIR"

STAMP="$(date +%Y%m%dT%H%M%S)"
TMP="$ROOT/results/_bundle_$STAMP"
mkdir -p "$TMP/scripts" "$TMP/docs"

# minimal payload (Windows-first + Linux parity)
cp -f "$ROOT/scripts/run.ps1"                      "$TMP/scripts/"
cp -f "$ROOT/scripts/validator_acceptance.ps1"     "$TMP/scripts/"
cp -f "$ROOT/scripts/kill_switch.ps1"              "$TMP/scripts/" 2>/dev/null || true
cp -f "$ROOT/scripts/run.sh"                       "$TMP/scripts/"
cp -f "$ROOT/scripts/validator_acceptance.sh"      "$TMP/scripts/"
cp -f "$ROOT/scripts/kill_switch.sh"               "$TMP/scripts/" 2>/dev/null || true
cp -f "$ROOT/scripts/check_ports.sh"               "$TMP/scripts/" 2>/dev/null || true
cp -f "$ROOT/scripts/install_and_run.ps1"          "$TMP/scripts/" 2>/dev/null || true
cp -f "$ROOT/scripts/install_and_run.sh"           "$TMP/scripts/" 2>/dev/null || true

cp -f "$ROOT/README.md"                            "$TMP/"
cp -f "$ROOT/docs/peer_validator_onboarding.md"    "$TMP/docs/" 2>/dev/null || true
cp -f "$ROOT/docs/compose_vs_bare_neo4j.md"        "$TMP/docs/" 2>/dev/null || true

# Windows-friendly top-level launcher
cat > "$TMP/START_WINDOWS.ps1" <<'PS'
Write-Host "=== Open-DARF · Start (Windows) ==="
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run.ps1
PS

# Linux-friendly top-level launcher
cat > "$TMP/start_linux.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf "===\n===\n===\n"
echo "=== Open-DARF · Start (Linux) ==="
bash ./scripts/run.sh
SH
chmod +x "$TMP/start_linux.sh"

# Archive (prefer zip; fallback to tar.gz)
BASENAME="open-darf-peer-bundle_$STAMP"
if command -v zip >/dev/null 2>&1; then
  (cd "$TMP/.." && zip -r "$OUTDIR/$BASENAME.zip" "$(basename "$TMP")" >/dev/null)
  echo "[✓] Bundle: $OUTDIR/$BASENAME.zip"
else
  (cd "$TMP/.." && tar -czf "$OUTDIR/$BASENAME.tar.gz" "$(basename "$TMP")")
  echo "[✓] Bundle: $OUTDIR/$BASENAME.tar.gz"
fi
