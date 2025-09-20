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
printf "===\n===\n===\n"
echo "=== Open-DARF · Port Inspector ==="
PORTS=(7474 7687 6333 6334 9000 9001 5432)
for p in "${PORTS[@]}"; do
  echo "-- :$p --"
  ss -ltnp "( sport = :$p )" 2>/dev/null | awk 'NR==1{next}{print}' || true
  command -v lsof >/dev/null 2>&1 && lsof -i :"$p" -n -P 2>/dev/null | sed -e '1,1d' || true
done
