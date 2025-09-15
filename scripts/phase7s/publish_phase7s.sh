#!/usr/bin/env bash
set -euo pipefail
TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUTDIR="var/releases/phase7s"
mkdir -p "$OUTDIR"

# Latest evidence tag (v7s-evidence-*)
TAG="$(git describe --tags --abbrev=0 --match 'v7s-evidence-*' 2>/dev/null || true)"
if [[ -z "$TAG" ]]; then
  echo "[error] No v7s-evidence-* tag found"; exit 20
fi

# Locate artifacts
BUNDLE="$(ls -1t var/reports/phase7s/phase7s_evidence_bundle_*.tar.gz | head -n1)"
MANIFEST="$(ls -1t var/reports/phase7s/MANIFEST_*.txt | head -n1)"
ACC_MD="$(ls -1t var/reports/phase7s/acceptance_status_*.md | head -n1)"
REL_NOTES="docs/phase7s/RELEASE_NOTES_7S.md"

[[ -f "$BUNDLE" ]] || { echo "[error] bundle not found"; exit 21; }

SHA="$(sha256sum "$BUNDLE" | awk '{print $1}')"
SIZE="$(stat -c %s "$BUNDLE" 2>/dev/null || echo "")"

BODY="$OUTDIR/GITHUB_RELEASE_${TAG}.md"

# Build a concise release body
{
  echo "# Phase 7S — Evidence Release"
  echo
  echo "- Tag: ${TAG}"
  echo "- Bundle: ${BUNDLE}"
  echo "- Manifest: ${MANIFEST:-n/a}"
  echo "- sha256: ${SHA}"
  echo "- size (bytes): ${SIZE}"
  echo
  echo "## Acceptance Snapshot (top)"
  if [[ -f "$ACC_MD" ]]; then
    sed -n '1,20p' "$ACC_MD"
  else
    echo "(no acceptance md found)"
  fi
  echo
  echo "## Full Release Notes"
  if [[ -f "$REL_NOTES" ]]; then
    sed -n '1,120p' "$REL_NOTES"
  else
    echo "(no release notes found)"
  fi
} > "$BODY"

# Optional push (default dry-run)
PUSH="${PUSH:-0}"
if [[ "$PUSH" == "1" ]]; then
  echo "[push] pushing current branch and tag ${TAG} to origin…"
  git push -u origin "$(git rev-parse --abbrev-ref HEAD)"
  git push origin "${TAG}"
else
  echo "[dry-run] Set PUSH=1 to push current branch and tag to origin."
fi

echo "[ok] release body: $BODY"
