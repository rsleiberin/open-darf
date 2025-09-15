#!/usr/bin/env bash
set -euo pipefail
MANIFEST="${1:-var/reports/phase7t/manifest.json}"
echo "===\n===\n==="
echo "[verify] manifest=$MANIFEST"
test -f "$MANIFEST" || { echo "[fail] manifest not found"; exit 1; }
jq -e '.schema_version==1 and (.entries|type=="array") and (.manifest_sha256|type=="string")' "$MANIFEST" >/dev/null \
  && echo "[ok] manifest schema looks valid" || { echo "[fail] manifest schema invalid"; exit 2; }
echo "[next] To re-hash a subset: scripts/phase7t/hash_and_manifest.py PATHS..."
