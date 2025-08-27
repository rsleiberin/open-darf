#!/usr/bin/env bash
set -eE -o pipefail
trap - ERR EXIT RETURN DEBUG || true
OWNER_REPO="${OWNER_REPO:-rsleiberin/darf-source}"
INDEX="var/infodump/issues/_index.txt"

if ! command -v gh >/dev/null 2>&1; then
  echo "❌ GitHub CLI (gh) not found. Install: https://cli.github.com/" >&2
  exit 1
fi

gh repo set-default "$OWNER_REPO" >/dev/null 2>&1 || true

while IFS='|' read -r path title labels; do
  [ -n "$path" ] || continue
  args=()
  IFS=',' read -r -a arr <<< "$labels"
  for L in "${arr[@]}"; do args+=("--label" "$L"); done
  echo "==> Creating: $title"
  gh issue create --title "$title" --body-file "$path" "${args[@]}"
done < "$INDEX"

echo "✓ All issues created for $OWNER_REPO"
