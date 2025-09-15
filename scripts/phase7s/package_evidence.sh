#!/usr/bin/env bash
set -euo pipefail

TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUTDIR="var/reports/phase7s"
mkdir -p "$OUTDIR"

BUNDLE="$OUTDIR/phase7s_evidence_bundle_${TS}.tar.gz"
TMPLIST="$(mktemp)"
MANIFEST="$OUTDIR/MANIFEST_${TS}.txt"
TOTLIST="$(mktemp)"

# Helper to add paths if they exist
add_glob() {
  local pattern="$1"
  shopt -s nullglob
  for f in $pattern; do
    if [[ -f "$f" ]]; then
      printf '%s\n' "$f" >> "$TMPLIST"
    fi
  done
  shopt -u nullglob
}

# Collect artifacts (idempotent; skip missing)
add_glob "var/reports/phase7s/validation_summary.json"
add_glob "var/reports/phase7s/validation_summary.md"
add_glob "open-darf/var/receipts/open-darf/oneclick_*.json"
add_glob "open-darf/open-darf-report-*.tar.gz"
add_glob "./open-darf-report-*.tar.gz"

# Key docs for provenance
add_glob "docs/architecture/branch_consolidation_plan.md"
add_glob "docs/architecture/post_grant_integration_roadmap.md"
add_glob "docs/phase7s/G2_NATIVE_UBUNTU_GATE.md"
add_glob "open-darf/docs/README.md"
add_glob "open-darf/docs/TROUBLESHOOTING.md"

# Scripts referenced in evidence path
add_glob "scripts/phase7s/aggregate_evidence.py"
add_glob "scripts/phase7s/aggregate_evidence.sh"
add_glob "open-darf/install.sh"
add_glob "open-darf/scripts/oneclick.sh"
add_glob "open-darf/scripts/quickstart.sh"
add_glob "open-darf/bin/doctor.sh"
add_glob "open-darf/validate/generate_evidence.sh"
add_glob "open-darf/validate/run_minimal.sh"

# Build MANIFEST with sha256 and size
{
  echo "# Phase 7S Evidence Manifest"
  echo "# Timestamp: ${TS}"
  echo ""
  if [[ -s "$TMPLIST" ]]; then
    while IFS= read -r f; do
      if [[ -f "$f" ]]; then
        sz=$(stat -c %s "$f" 2>/dev/null || echo 0)
        sh=$(sha256sum "$f" 2>/dev/null | awk '{print $1}')
        printf "%-64s  %12s  %s\n" "${sh:-N/A}" "${sz}" "$f"
      fi
    done < "$TMPLIST"
  else
    echo "(no artifacts found)"
  fi
} > "$MANIFEST"

# Combine filelist + manifest and package
cat "$TMPLIST" > "$TOTLIST"
printf '%s\n' "$MANIFEST" >> "$TOTLIST"

tar -czf "$BUNDLE" -T "$TOTLIST"

echo "[bundle] created -> $BUNDLE"
echo "[manifest]        $MANIFEST"
sha256sum "$BUNDLE" || true

# Cleanup temp files
rm -f "$TMPLIST" "$TOTLIST"

exit 0
