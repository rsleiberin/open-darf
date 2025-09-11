#!/usr/bin/env bash
set -euo pipefail
# Restore working directory
cd "$(dirname "$0")"
# Show current state
echo "=== DARF resume ==="
pwd
echo "--- git status (if repo) ---"
git status 2>/dev/null || echo "(no git repo detected)"
echo "--- decisions ---"
ls -1 docs/decisions 2>/dev/null || true
echo "--- audits ---"
ls -1 docs/audit 2>/dev/null || true
echo "Ready to resume at: Phase 7N runtime pivot decision (Podman v4 on 22.04 vs Docker interim)."
