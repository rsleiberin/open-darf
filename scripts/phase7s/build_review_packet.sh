#!/usr/bin/env bash
set -euo pipefail
TS="$(date -u +%Y%m%dT%H%M%SZ)"
BASE="var/releases/phase7s"
STAGE="var/releases/_stage_review_${TS}"
OUT="${BASE}/review_packet_${TS}.tar.gz"
SUM="${BASE}/review_packet_${TS}.sha256"
mkdir -p "$BASE" "$STAGE"

# Resolve latest artifacts
latest_bundle="$(ls -1t var/reports/phase7s/phase7s_evidence_bundle_*.tar.gz 2>/dev/null | head -n1 || true)"
latest_manifest="$(ls -1t var/reports/phase7s/MANIFEST_*.txt 2>/dev/null | head -n1 || true)"
latest_accept_md="$(ls -1t var/reports/phase7s/acceptance_status_*.md 2>/dev/null | head -n1 || true)"
latest_accept_json="${latest_accept_md%.md}.json"

# Files to include (if present)
declare -a FILES=(
  "docs/phase7s/RELEASE_NOTES_7S.md"
  "docs/phase7s/FINAL_REPORT.md"
  "docs/phase7s/INDEX.md"
  "docs/phase7s/GRANT_SUBMISSION_README.md"
  "docs/phase7s/COLLAB_INVITE.md"
  "var/reports/phase7s/validation_summary.json"
  "var/reports/phase7s/validation_summary.md"
  "var/reports/phase7s/timing_summary.json"
  "var/reports/phase7s/timing_summary.md"
)

# Append dynamic ones if they exist
[[ -n "$latest_bundle" && -f "$latest_bundle" ]] && FILES+=("$latest_bundle")
[[ -n "$latest_manifest" && -f "$latest_manifest" ]] && FILES+=("$latest_manifest")
[[ -n "$latest_accept_md" && -f "$latest_accept_md" ]] && FILES+=("$latest_accept_md")
[[ -f "$latest_accept_json" ]] && FILES+=("$latest_accept_json")

# Stage files preserving paths
shopt -s nullglob
for f in "${FILES[@]}"; do
  if [[ -f "$f" ]]; then
    dst="${STAGE}/$(dirname "$f")"
    mkdir -p "$dst"
    cp -f "$f" "$dst/"
  fi
done

# Add a VERIFY.txt with quick commands
VERIFY="${STAGE}/VERIFY.txt"
{
  echo "Phase 7S Review Packet — ${TS}"
  echo ""
  echo "Included:"
  for f in "${FILES[@]}"; do [[ -f "$f" ]] && echo " - $f"; done
  echo ""
  echo "Quick checks:"
  echo "  sha256sum ${OUT##*/}"
  echo "  less docs/phase7s/RELEASE_NOTES_7S.md"
  echo "  less docs/phase7s/FINAL_REPORT.md"
} > "$VERIFY"

# Create tarball (relative to STAGE parent to preserve paths under var/ and docs/)
tar -czf "$OUT" -C "var/releases" "_stage_review_${TS}/." --transform "s|^_stage_review_${TS}/||"
sha256sum "$OUT" | tee "$SUM"

echo "[packet] $OUT"
echo "[sha256] $SUM"
