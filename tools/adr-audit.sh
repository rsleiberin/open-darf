#!/usr/bin/env bash
set -euo pipefail
ROOT="${1:-docs/decisions}"
source tools/lib/adr_parse.sh
ALLOWED="CON VEN ARC INT RSH KNO ALG VAL SYN DAT PER API AGT SWM FRD EDU UX UI ACC BIZ LEG ETH LIC SEC OPS GOV PRC QUA DOC META EVO EXP FUT"

find "$ROOT" -maxdepth 1 -type f -name 'ADR-*.md' -print0 | sort -z | while IFS= read -r -d '' f; do
  id="$(basename "$f" .md)"
  t="$(adr_type_from_id "$id" || true)"

  # Must start with YAML front-matter
  if ! head -n1 "$f" | grep -qx -- '---'; then
    echo "ERR: $id missing YAML front-matter (first line '---')"
    continue
  fi

  # Read YAML keys from first front-matter block only
  ytype="$(awk '/^---/{y++} y==1 && /^type:/{print $2}' "$f" | head -n1 || true)"
  status="$(awk '/^---/{y++} y==1 && /^status:/{print $2}' "$f" | head -n1 || true)"
  skip="$(awk '/^---/{y++} y==1 && /^skip_audit:/{print $2}' "$f" | head -n1 || true)"

  # Skip rules
  if [[ "$skip" == "true" ]]; then
    echo "SKIP: $id (skip_audit:true)"
    continue
  fi
  if [[ "$status" == "blocked" ]]; then
    echo "SKIP: $id (status:blocked)"
    continue
  fi

  # Validate basics
  [ -z "$ytype" ] && { echo "ERR: $id missing 'type:' in YAML"; continue; }
  grep -qw -- "$t" <<<"$ALLOWED" || echo "WARN: $id filename type '$t' not in allowed 33-type set"
  [ "$ytype" = "$t" ] || echo "WARN: $id YAML.type='$ytype' != filename.type='$t'"
done
