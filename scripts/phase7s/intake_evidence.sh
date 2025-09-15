#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: $0 <file1> [file2 ...]" >&2
  exit 2
}

[[ $# -ge 1 ]] || usage

mkdir -p community_intake/{queue,accepted,rejected} var/receipts/community
TS="$(date -u +%Y%m%dT%H%M%SZ)"

has_jq=0
if command -v jq >/dev/null 2>&1; then has_jq=1; fi

for f in "$@"; do
  if [[ ! -f "$f" ]]; then
    echo "[skip] missing: $f"
    continue
  fi
  base="$(basename "$f")"
  ext="${base##*.}"
  sz="$(stat -c %s "$f" 2>/dev/null || echo 0)"
  sha="$(sha256sum "$f" 2>/dev/null | awk '{print $1}')"

  case "$base" in
    *.tar.gz)
      dest="community_intake/accepted/${base%.tar.gz}_$TS"
      mkdir -p "$dest"
      cp -n "$f" "$dest/"
      (cd "$dest" && tar -xzf "$base" || true)

      # Attempt to parse known files
      sys_json="$dest/system_snapshot.json"
      torch_json="$dest/torch_probe.json"
      distro="unknown"; kernel="unknown"; cuda="unknown"

      if [[ $has_jq -eq 1 && -f "$sys_json" ]]; then
        distro="$(jq -r '.distro // "unknown"' "$sys_json" 2>/dev/null || echo unknown)"
        kernel="$(jq -r '.kernel // "unknown"' "$sys_json" 2>/dev/null || echo unknown)"
      fi
      if [[ $has_jq -eq 1 && -f "$torch_json" ]]; then
        cuda="$(jq -r '.cuda_available // "unknown"' "$torch_json" 2>/dev/null || echo unknown)"
      fi

      rcpt="var/receipts/community/intake_${base%.tar.gz}_$TS.json"
      {
        echo "{"
        echo "  \"type\": \"tarball\","
        echo "  \"timestamp\": \"$TS\","
        echo "  \"source_file\": \"$f\","
        echo "  \"sha256\": \"$sha\","
        echo "  \"size_bytes\": $sz,"
        echo "  \"dest_dir\": \"$dest\","
        echo "  \"parsed\": { \"distro\": \"$distro\", \"kernel\": \"$kernel\", \"cuda_available\": \"$cuda\" }"
        echo "}"
      } > "$rcpt"
      echo "[ok] intake tarball -> $rcpt"
      ;;
    *.json)
      dest="community_intake/accepted/${base%.*}_$TS.json"
      cp -n "$f" "$dest"
      rcpt="var/receipts/community/intake_${base%.*}_$TS.json"
      if [[ $has_jq -eq 1 ]]; then
        host="$(jq -r '.host // "unknown"' "$f" 2>/dev/null || echo unknown)"
        distro="$(jq -r '.distro // "unknown"' "$f" 2>/dev/null || echo unknown)"
      else
        host="unknown"; distro="unknown"
      fi
      {
        echo "{"
        echo "  \"type\": \"receipt-json\","
        echo "  \"timestamp\": \"$TS\","
        echo "  \"source_file\": \"$f\","
        echo "  \"sha256\": \"$sha\","
        echo "  \"size_bytes\": $sz,"
        echo "  \"host\": \"$host\","
        echo "  \"distro\": \"$distro\","
        echo "  \"dest_file\": \"$dest\""
        echo "}"
      } > "$rcpt"
      echo "[ok] intake receipt -> $rcpt"
      ;;
    *)
      echo "[reject] unsupported file type: $f"
      mv -n "$f" "community_intake/rejected/${base}_$TS" || true
      ;;
  esac
done
