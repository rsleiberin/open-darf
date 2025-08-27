#!/usr/bin/env bash
set -eE -o pipefail
trap - ERR EXIT RETURN DEBUG || true

BRANCH="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo main)"
STAMP="$(date -u +%Y%m%d-%H%M%S)"
NAME="salvage/${BRANCH}-${STAMP}"

DO_COMMIT="${DO_COMMIT:-0}"   # 1 => git add -A && commit (if changes)
PUSH="${PUSH:-0}"             # 1 => push salvage branch to origin

git fetch --prune || true
git switch -c "$NAME"
if [ "$DO_COMMIT" = "1" ]; then
  if ! git diff --quiet || ! git diff --cached --quiet; then
    git add -A
    git commit -m "salvage: snapshot on ${STAMP} from ${BRANCH}"
  fi
fi
if [ "$PUSH" = "1" ]; then
  git push -u origin "$NAME" || true
fi
echo "✓ Salvage branch ready: $NAME"
