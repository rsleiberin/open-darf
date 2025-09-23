#!/usr/bin/env bash
set -euo pipefail
PR="${1:?PR number required}"
REPO="${REPO:-$(gh repo view --json nameWithOwner -q .nameWithOwner)}"
TITLE="$(gh pr view "$PR" --repo "$REPO" --json title -q .title)"
BASE="$(gh pr view "$PR" --repo "$REPO" --json baseRefName -q .baseRefName)"
HEAD="$(gh pr view "$PR" --repo "$REPO" --json headRefName -q .headRefName)"
COMMITS="$(gh pr view "$PR" --repo "$REPO" --json commits -q '.commits[].messageHeadline')"

echo END_OF_LOG
echo
echo "- PR #$PR: $TITLE"
echo "- Branch: $HEAD -> $BASE"
echo "- Repo: $REPO"
echo
echo "Commits:"
while IFS= read -r line; do
  [[ -n "$line" ]] && echo "  - $line"
done <<< "$COMMITS"
echo
echo "Summary:"
echo "- What shipped: RNL theory docs and END_OF_LOG pipeline"
echo "- Blockers: none"
echo "- Pointers: docs/theory/*, .github/workflows/end_of_log.yml"
