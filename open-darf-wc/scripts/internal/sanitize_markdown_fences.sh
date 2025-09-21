#!/usr/bin/env bash
set -euo pipefail
ROOT="${1:-$PWD}"
STAMP="$(date +%Y%m%dT%H%M%S)"
BACKUP_DIR="${ROOT%/}/.cache/md_fence_backup_${STAMP}"
mkdir -p "$BACKUP_DIR"
shopt -s nullglob

# exclude heavy/unreadable and generated paths
mapfile -t FILES < <(
  find "$ROOT" \
    -type d \( -path "$ROOT/.git" -o -path "$ROOT/node_modules" -o -path "$ROOT/results" -o -path "$ROOT/.cache" -o -path "$ROOT/infra/neo4j/init" \) -prune -o \
    -type f \( -name "*.md" -o -name "*.mdx" \) -readable -print 2>/dev/null
)

changed=0
for f in "${FILES[@]}"; do
  # only operate if a 3-backtick fence is present
  if grep -q '```' "$f" 2>/dev/null; then
    rel="${f#$ROOT/}"
    mkdir -p "$BACKUP_DIR/$(dirname "$rel")"
    cp -f "$f" "$BACKUP_DIR/$rel"
    # Replace opening/closing triple-backtick fences (at line start) with tildes
    sed -E 's/^```([A-Za-z0-9_-]*)[[:space:]]*$/~~~\1/g; s/^```[[:space:]]*$/~~~/g' "$f" > "$f.tmp"
    mv "$f.tmp" "$f"
    changed=$((changed+1))
    echo "[SANITIZE] $rel"
  fi
done
echo "[SANITIZE] files_changed=$changed backup=$BACKUP_DIR"
