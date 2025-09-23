#!/usr/bin/env bash
set -euo pipefail
declare -a CF=()
[[ -f ops/compose/compose.yml ]] && CF+=( -f ops/compose/compose.yml )
[[ -f ops/compose/compose.health.yml ]] && CF+=( -f ops/compose/compose.health.yml )
[[ -f ops/compose/compose.override.yml ]] && CF+=( -f ops/compose/compose.override.yml )
printf '%s\0' "${CF[@]}"
