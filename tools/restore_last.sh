#!/usr/bin/env bash
set -Eeuo pipefail
cd "$(git rev-parse --show-toplevel)"
git restore --worktree --source=HEAD \
  docs/audit/pipeline/pipeline_cbdt/_last \
  docs/audit/pipeline/pipeline_oscar/_last \
  docs/audit/pipeline/pipeline_prov/_last || true
echo "Restored tracked _last/ mirrors to HEAD."
