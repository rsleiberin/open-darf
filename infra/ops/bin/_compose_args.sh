#!/usr/bin/env bash
set -euo pipefail
shopt -s nullglob

# Candidate list (ordered). Hardcoded names are only included if -f succeeds.
CANDIDATES=(
  "ops/compose/docker-compose.yml"
  "ops/compose/docker-compose.yaml"
  "ops/compose/compose.yml"
  "ops/compose/compose.yaml"
)

# Also include any other yml/yaml in ops/compose/* that are not duplicates.
for g in ops/compose/*.yml ops/compose/*.yaml; do
  CANDIDATES+=("$g")
done

declare -a UNIQUE=()
declare -A SEEN=()

for f in "${CANDIDATES[@]}"; do
  # Skip non-files and duplicates
  [[ -f "$f" ]] || continue
  [[ -n "${SEEN[$f]:-}" ]] && continue
  SEEN["$f"]=1
  UNIQUE+=("$f")
done

if ((${#UNIQUE[@]}==0)); then
  echo "ERROR: no compose files found under ops/compose" >&2
  exit 2
fi

# Emit args for docker compose and also a human-readable list on stderr
printf "Selected compose files:\\n" >&2
for f in "${UNIQUE[@]}"; do
  printf "  - %s\\n" "$f" >&2
  printf " -f %q" "$f"
done
