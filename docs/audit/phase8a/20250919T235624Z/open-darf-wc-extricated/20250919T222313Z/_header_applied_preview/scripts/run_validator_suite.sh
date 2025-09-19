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
source "./scripts/_hb.sh"

printf "===\n===\n===\n"
echo "=== Open-DARF · Validator Suite Runner (Linux) ==="

# Optional: start stack if not running
need_start=0
for n in darf-minio darf-qdrant darf-postgres darf-neo4j; do
  docker ps -q --filter "name=^${n}$" | grep -q . || { need_start=1; break; }
done
if [ "$need_start" -eq 1 ]; then
  echo "[Info] Stack not fully running; starting via scripts/run.sh"
  bash ./scripts/run.sh
fi

# Run acceptance
bash ./scripts/validator_acceptance.sh
