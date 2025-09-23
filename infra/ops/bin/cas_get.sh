#!/usr/bin/env bash
set -euo pipefail
if [[ $# -lt 2 ]]; then echo "usage: cas_get.sh <sha256> <out_path>" >&2; exit 2; fi
hash="$1"; out="$2"
mkdir -p "$(dirname "$out")"
# Stream from MinIO to stdout; host redirects into 'out'
ops/bin/mc_host.sh cat "local/cas/$hash" > "$out"
echo "[cas_get] wrote: $out" >&2
