#!/usr/bin/env bash
set -euo pipefail

TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUTDIR="var/releases/open-darf"
STAGE="var/releases/_stage_open_darf_${TS}"
mkdir -p "$OUTDIR" "$STAGE"

echo "[stage] assembling Open-DARF minimal into $STAGE"
rsync -a --delete --exclude 'var/' --exclude '.git' open-darf/ "$STAGE/open-darf/"

# Include top-level docs if present
mkdir -p "$STAGE/docs"
for f in docs/phase7s/COMMUNITY_VALIDATION.md docs/phase7s/GRANT_SUBMISSION_README.md; do
  [[ -f "$f" ]] && install -D -m 0644 "$f" "$STAGE/$f"
done

# Provenance file
mkdir -p "$STAGE/meta"
{
  echo "{"
  echo "  \"timestamp\": \"${TS}\","
  echo "  \"git_head\": \"$(git rev-parse HEAD)\","
  echo "  \"tag\": \"$(git describe --tags --abbrev=0 2>/dev/null || echo none)\""
  echo "}"
} > "$STAGE/meta/provenance.json"

# License/NOTICE if present
for f in LICENSE NOTICE; do
  [[ -f "$f" ]] && install -D -m 0644 "$f" "$STAGE/$f"
done

ARCHIVE="${OUTDIR}/open-darf_minimal_${TS}.tar.gz"
echo "[package] creating ${ARCHIVE}"
tar -czf "$ARCHIVE" -C "$STAGE" .

# Checksums manifest
MAN="${OUTDIR}/open-darf_minimal_${TS}.sha256"
sha256sum "$ARCHIVE" > "$MAN"

echo "[ok] Release kit:"
echo "  archive : $ARCHIVE"
echo "  sha256  : $(cut -d' ' -f1 "$MAN")"
