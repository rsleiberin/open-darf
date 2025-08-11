#!/usr/bin/env bash
set -Ee -o pipefail

# Directories to check
DIRS=("docs/reference" "docs/theory")

# 1) Fail on exec-labeled code fences
if grep -RIn --include="*.md" -E '```(bash|sh|zsh|python|javascript|js|ts|typescript)\b' "${DIRS[@]}" | sed 's/^/ERR(exec fence): /'; then
  echo "✗ Found exec-labeled fences in reference/theory. Use 4-space indentation or non-exec labels (text/example/pseudo/console)."
  exit 1
fi

# 2) Warn on unlabeled triple-backticks (encourage non-exec labels or indentation)
if grep -RIn --include="*.md" -E '^```$' "${DIRS[@]}" | sed 's/^/WARN(unlabeled fence): /'; then
  echo "⚠ Unlabeled fences found; prefer 4-space indentation or explicit non-exec labels."
fi

# 3) Enforce allowed non-exec labels if used
if grep -RIn --include="*.md" -E '^```([A-Za-z0-9_-]+)$' "${DIRS[@]}" | \
   grep -vE '^```(text|example|pseudo|console)$' | sed 's/^/ERR(disallowed label): /'; then
  echo "✗ Only non-exec labels allowed in reference/theory: text, example, pseudo, console."
  exit 1
fi

# 4) Optional: check for missing disclaimers at top of illustrative docs in docs/theory
missing=0
for f in $(git ls-files 'docs/theory/*.md'); do
  if ! head -n2 "$f" | grep -q '⚠️ Examples only — not runnable'; then
    echo "WARN(disclaimer): $f is missing the two-line disclaimer."
    missing=1
  fi
done
(( missing == 0 )) || echo "⚠ Add the standard disclaimer to theory docs with examples."

echo "✓ RNL fence validation passed."
