#!/usr/bin/env bash
# stdout: TYPE or empty; handles ADR-YYMM-TYPE-NNN and ADR-TYPE-NNN
adr_type_from_id() {
  local id="$1"
  if [[ "$id" =~ ^ADR-[0-9]{4}-([A-Z]+)-[0-9]+ ]]; then echo "${BASH_REMATCH[1]}"; return 0; fi
  if [[ "$id" =~ ^ADR-([A-Z]+)-[0-9]+ ]]; then echo "${BASH_REMATCH[1]}"; return 0; fi
  return 1
}
