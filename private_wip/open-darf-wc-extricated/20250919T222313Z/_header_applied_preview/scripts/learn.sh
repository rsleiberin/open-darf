# DO NOT COMMIT THIS FILE — PREVIEW OF PROPOSED HEADER
# Header: Purpose
# One or two plain sentences describing what this file does and who runs it.

# Header: Inputs
# - Environment variables / CLI flags
# - External services called (if any)

# Header: Outputs
# - Files/receipts generated
# - Network side effects (ports/endpoints touched)

# Header: Data Flow
# Source → Transform/Validation → Sink (mention receipts directory)

# Header: Failure Modes & Recovery
# Common errors, detection cues, and operator actions.

# Header: Idempotence & Teardown
# What is safe to re-run; cleanup behavior.

# Header: Security & Privacy Notes
# Sensitive ops (if any). Stays local unless explicit user consent for publishing evidence.

#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
printf "===\n===\n===\n"
echo "=== Open-DARF · Learning Module (Linux) ==="
for f in docs/learning/lesson_01_introduction.md docs/learning/lesson_02_docker_stack.md docs/learning/lesson_03_constitutional_ai.md; do
  echo
  echo "---- $(basename "$f") ----"
  sed -n '1,80p' "$f" | sed -e 's/^# .*$/[Lesson]/'
done
echo
echo "[✓] More: open docs/learning/* in your editor."
