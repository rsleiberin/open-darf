#!/usr/bin/env bash
set -euo pipefail
# Usage: tri_state_validator.sh <file>
in="$1"
ts="$(date -Is)"
start_ns() { if date +%s%N >/dev/null 2>&1; then date +%s%N; else echo $(( $(date +%s)*1000000000 )); fi; }
st_ns="$(start_ns)"

decision="ALLOW"
declare -a reasons=()

# Guards
if [[ ! -f "$in" ]]; then
  decision="DENY"; reasons+=("not_a_file")
fi

policy="docs/policy/constitution.json"
if [[ ! -f "$policy" ]]; then
  decision="DENY"; reasons+=("missing_policy")
fi

filename="$(basename -- "$in")"
ext=".${filename##*.}"; [[ "$filename" == "$ext" ]] && ext=""
bytes=0; sha=""
if [[ "$decision" != "DENY" ]]; then
  bytes="$(stat -c%s "$in" 2>/dev/null || echo 0)"
  sha="$(sha256sum "$in" 2>/dev/null | awk '{print $1}')"
fi

# Parse policy (portable, no jq)
max_bytes="$(grep -o '"max_bytes":[^,]*' "$policy" 2>/dev/null | awk -F: '{gsub(/[[:space:]]/,"",$2); print $2}')"
[[ -z "$max_bytes" ]] && max_bytes=0
pending_unknown="$(grep -o '"pending_on_unknown_ext":[^,]*' "$policy" 2>/dev/null | awk -F: '{gsub(/[[:space:]]/,"",$2); print tolower($2)}')"
allow_exts="$(sed -n '/"allow_extensions"/,/\]/p' "$policy" 2>/dev/null | grep -oE '"\.[^"]+"' | tr -d '"')"
deny_patterns_file="$(mktemp)"
trap 'rm -f "$deny_patterns_file"' EXIT
sed -n '/"deny_patterns"/,/\]/p' "$policy" 2>/dev/null | sed -n 's/.*"\(.*\)".*/\1/p' > "$deny_patterns_file"

# Size rule
if (( bytes > max_bytes )); then
  decision="DENY"; reasons+=("size_gt_max")
fi

# Extension rule
is_allowed=0
while read -r e; do
  [[ -z "$e" ]] && continue
  if [[ "$ext" == "$e" ]]; then is_allowed=1; break; fi
done <<< "$allow_exts"

if (( is_allowed == 0 )); then
  if [[ "$pending_unknown" == "true" && "$decision" != "DENY" ]]; then
    decision="PENDING"; reasons+=("unknown_extension")
  else
    decision="DENY"; reasons+=("unknown_extension")
  fi
fi

# Deny-pattern scan (fixed-string, small files only)
if (( bytes <= 1048576 )) && [[ -s "$deny_patterns_file" ]]; then
  if LC_ALL=C grep -a -F -m1 -f "$deny_patterns_file" "$in" >/dev/null 2>&1; then
    decision="DENY"; reasons+=("deny_pattern_match")
  fi
fi

end_ns() { if date +%s%N >/dev/null 2>&1; then date +%s%N; else echo $(( $(date +%s)*1000000000 )); fi; }
ed_ns="$(end_ns)"; lat_ms=$(( (ed_ns - st_ns)/1000000 ))

# Receipt
out="docs/evidence/constitution/receipt_${sha:-unknown}_$(date +%s).json"
mkdir -p "$(dirname "$out")"
{
  printf '{'
  printf '"timestamp":"%s",' "$ts"
  printf '"filename":"%s",' "$filename"
  printf '"sha256":"%s",' "${sha:-unknown}"
  printf '"bytes":%s,' "$bytes"
  printf '"decision":"%s",' "$decision"
  printf '"latency_ms":%s,' "$lat_ms"
  printf '"reasons":['
  for i in "${!reasons[@]}"; do
    printf '%s"%s"' $([[ $i -gt 0 ]] && echo ,) "${reasons[$i]}"
  done
  printf ']'
  printf '}'
} > "$out"
echo "[validator] wrote: $out" >&2
echo "$decision"
