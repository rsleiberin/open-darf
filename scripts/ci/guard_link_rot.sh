#!/usr/bin/env bash
set -euo pipefail
git ls-files '*.md' '*.adoc' 2>/dev/null | xargs -I{} grep -nH -E '(http|https)://' {} || true
exit 0
