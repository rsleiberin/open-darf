#!/usr/bin/env bash
set -euo pipefail

manifest="${1:?usage: $0 manifest.jsonl}"

# Read the file as raw lines (-R), try to JSON-decode each line (fromjson?),
# drop non-JSON lines (// empty), then extract a content digest from several
# possible fields and normalize away any "sha256:" prefix.
leaves="$(
  jq -Rr '
    fromjson? // empty
    | select((.deleted // false) | not)
    | . as $rec
    | (
        $rec.sha256
        // $rec.content_sha256
        // $rec.blob_sha256
        // $rec.content_hash
        // $rec.hash
        // $rec.digest
        // $rec.cas_key
        // ($rec.cas // empty | .sha256 // .content_sha256 // .key)
      )
    | select(. != null and . != "")
    | sub("^sha256:";"") | sub("^SHA256:";"")
  ' "$manifest"
)"

# Count leaves
count=$(awk 'END{print NR}' <<<"$leaves")

# Multiplicity-sensitive, order-independent root.
if [[ "$count" -eq 0 ]]; then
  root=$(printf '' | sha256sum | awk '{print $1}')
else
  root=$(printf '%s\n' "$leaves" | LC_ALL=C sort | sha256sum | awk '{print $1}')
fi

printf '%s %d\n' "$root" "$count"
