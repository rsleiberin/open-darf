#!/usr/bin/env bash
set -Eeuo pipefail
paths=(docs/reference docs/theory)
# Disallow runnable fences that imply execution
bad_re='^```(bash|sh|zsh|python|javascript|js|ts|typescript)\s*$'
# Allowed alternatives: ```text, ```example, ```pseudo, ```console, or 4-space indent
fail=0
for p in "${paths[@]}"; do
  [ -d "$p" ] || continue
  while IFS= read -r -d '' f; do
    if grep -nE "$bad_re" "$f" >/dev/null; then
      echo ":: ERROR in $f"
      echo "   Use non-exec fences: \`\`\`text | \`\`\`example | \`\`\`pseudo | \`\`\`console"
      echo "   Or indent by 4 spaces. Do not use \`\`\`bash/\`\`\`python etc. in reference/theory docs."
      echo
      grep -nE "$bad_re" "$f" || true
      fail=1
    fi
  done < <(find "$p" -type f -name '*.md' -print0)
done
exit "$fail"
