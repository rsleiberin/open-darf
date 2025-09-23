#!/usr/bin/env bash
set -euo pipefail
# usage: compare_manifests.sh <old.jsonl> <new.jsonl>
old="$1"; new="$2"
[[ -f "$old" && -f "$new" ]] || { echo "[compare] missing files" >&2; exit 2; }

# Build maps: sha->path (first occurrence) and sets of sha
awk -v o="$old" '
  BEGIN{FS="[:\",{}]+"}
  { while ( (match($0, /"path":"([^"]+)".*"sha256":"([a-f0-9]{64})"/, m)) ) {
      path=m[1]; sha=m[2];
      if (!(sha in os)) os[sha]=path;
      osh[sha]=1;
      sub(/"path":"[^"]+"/,"", $0); sub(/"sha256":"[a-f0-9]{64}"/,"", $0);
    }
  }
  END{
    for (k in os) { printf("O\t%s\t%s\n", k, os[k]); }
  }
' "$old" > /tmp/m_old.$$

awk -v n="$new" '
  BEGIN{FS="[:\",{}]+"}
  { while ( (match($0, /"path":"([^"]+)".*"sha256":"([a-f0-9]{64})"/, m)) ) {
      path=m[1]; sha=m[2];
      if (!(sha in ns)) ns[sha]=path;
      nsh[sha]=1;
      sub(/"path":"[^"]+"/,"", $0); sub(/"sha256":"[a-f0-9]{64}"/,"", $0);
    }
  }
  END{
    for (k in ns) { printf("N\t%s\t%s\n", k, ns[k]); }
  }
' "$new" > /tmp/m_new.$$

# Join on sha
declare -A opath npath
while IFS=$'\t' read -r tag sha p; do
  opath["$sha"]="$p"
done < /tmp/m_old.$$
while IFS=$'\t' read -r tag sha p; do
  npath["$sha"]="$p"
done < /tmp/m_new.$$

adds=() dels=() renames=() stays=()

# Detect additions/deletions/renames
for sha in "${!opath[@]}"; do
  if [[ -z "${npath[$sha]:-}" ]]; then
    dels+=("$sha|${opath[$sha]}")
  else
    if [[ "${opath[$sha]}" != "${npath[$sha]}" ]]; then
      renames+=("$sha|${opath[$sha]}|${npath[$sha]}")
    else
      stays+=("$sha|${opath[$sha]}")
    fi
  fi
done
for sha in "${!npath[@]}"; do
  if [[ -z "${opath[$sha]:-}" ]]; then
    adds+=("$sha|${npath[$sha]}")
  fi
done

# Output summary as human text + JSON evidence
echo "[compare] adds:${#adds[@]} dels:${#dels[@]} renames:${#renames[@]} unchanged:${#stays[@]}"
epoch="$(date +%s)"
out="docs/evidence/ingest/diff_${epoch}.json"
mkdir -p "$(dirname "$out")"

{
  printf '{"old":"%s","new":"%s",' "$old" "$new"
  printf '"adds":['
  for i in "${!adds[@]}"; do
    IFS='|' read -r s p <<< "${adds[$i]}"; printf '%s{"sha256":"%s","path":"%s"}' $([[ $i -gt 0 ]] && echo ,) "$s" "$p"
  done
  printf '],"deletes":['
  for i in "${!dels[@]}"; do
    IFS='|' read -r s p <<< "${dels[$i]}"; printf '%s{"sha256":"%s","path":"%s"}' $([[ $i -gt 0 ]] && echo ,) "$s" "$p"
  done
  printf '],"renames":['
  for i in "${!renames[@]}"; do
    IFS='|' read -r s po pn <<< "${renames[$i]}"; printf '%s{"sha256":"%s","from":"%s","to":"%s"}' $([[ $i -gt 0 ]] && echo ,) "$s" "$po" "$pn"
  done
  printf ']}'
} > "$out"

echo "[compare] wrote: $out"
