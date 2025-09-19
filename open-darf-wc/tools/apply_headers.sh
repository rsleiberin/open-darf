#!/usr/bin/env bash
set -euo pipefail
# Apply standard headers to real files using the preview mirror.
# Idempotent: skips files already containing "Header: Purpose" in first 80 lines.

usage() {
  echo "Usage: $0 <preview_root> <apply_list.tsv>"
  echo "Example: $0 ../_header_applied_preview ../docs/audit/phase7za/2025.../header_apply_list.tsv"
}

PREVIEW_ROOT="\${1:-}"
APPLY_LIST="\${2:-}"

[ -n "\$PREVIEW_ROOT" ] && [ -n "\$APPLY_LIST" ] || { usage; exit 2; }
[ -d "\$PREVIEW_ROOT" ] || { echo "[fatal] preview root not found: \$PREVIEW_ROOT" >&2; exit 3; }
[ -f "\$APPLY_LIST" ] || { echo "[fatal] apply list not found: \$APPLY_LIST" >&2; exit 4; }

ROOT="$(git rev-parse --show-toplevel 2>/dev/null)"
SUB="open-darf-wc"
cd "\$ROOT"

added=0; skipped=0; total=0
tail -n +2 "\$APPLY_LIST" | while IFS=$'\t' read -r file status preview_path; do
  total=\$((total+1))
  # Only act on "added_preview"
  [ "\$status" = "added_preview" ] || { echo "[skip] \$file (\$status)"; continue; }
  src="\$ROOT/\$file"
  rel_under_sub="\${file#\${SUB}/}"
  prev="\$PREVIEW_ROOT/\$rel_under_sub"

  if head -n 80 "\$src" | grep -q "Header: Purpose"; then
    echo "[skip] already has header: \$file"
    skipped=\$((skipped+1))
    continue
  fi

  if [ ! -f "\$prev" ]; then
    echo "[warn] missing preview for \$file at \$prev; skipping"
    skipped=\$((skipped+1))
    continue
  fi

  tmp="\$src.tmp.header"
  cp "\$prev" "\$tmp"
  mv "\$tmp" "\$src"
  echo "[ok] applied header -> \$file"
  added=\$((added+1))
done

echo "[summary] total=\$total added=\$added skipped=\$skipped"
