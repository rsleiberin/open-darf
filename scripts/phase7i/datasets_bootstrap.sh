#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
ENV_FILE="$ROOT/docs/phase7i/DATA_SOURCES.env"
DST="$ROOT/data"

load_env(){
  if [ -f "$ENV_FILE" ]; then
    # shellcheck disable=SC1090
    . "$ENV_FILE"
  fi
}

fetch(){
  local url="$1" out="$2"
  [ -z "$url" ] && return 0
  echo "[DL] $url -> $out"
  mkdir -p "$(dirname "$out")"
  if command -v curl >/dev/null 2>&1; then
    curl -fsSL "$url" -o "$out"
  elif command -v wget >/dev/null 2>&1; then
    wget -qO "$out" "$url"
  else
    echo "[WARN] Neither curl nor wget available; skipping $url"
    return 1
  fi
}

copy_if(){
  local src="$1" pattern="$2" dest="$3"
  [ -d "$src" ] || return 0
  mkdir -p "$dest"
  shopt -s nullglob
  local found=0
  for f in "$src"/$pattern; do
    found=1
    echo "[CP] $f -> $dest/"
    cp -f "$f" "$dest/"
  done
  shopt -u nullglob
  [ $found -eq 0 ] && echo "[INFO] No files matching $pattern in $src (ok)"
}

load_env

# Option A: downloads
fetch "${SCIERC_TRAIN_URL:-}" "$DST/scierc/train.jsonl" || true
fetch "${SCIERC_DEV_URL:-}"   "$DST/scierc/dev.jsonl"   || true
fetch "${SCIERC_TEST_URL:-}"  "$DST/scierc/test.jsonl"  || true

fetch "${BIORED_TRAIN_URL:-}" "$DST/biored/train.jsonl" || true
fetch "${BIORED_DEV_URL:-}"   "$DST/biored/dev.jsonl"   || true
fetch "${BIORED_TEST_URL:-}"  "$DST/biored/test.jsonl"  || true

# Option B: local copies
copy_if "${SCIERC_SRC_DIR:-}" "*train*.json*" "$DST/scierc"
copy_if "${SCIERC_SRC_DIR:-}" "*dev*.json*"   "$DST/scierc"
copy_if "${SCIERC_SRC_DIR:-}" "*test*.json*"  "$DST/scierc"

copy_if "${BIORED_SRC_DIR:-}" "*train*.json*" "$DST/biored"
copy_if "${BIORED_SRC_DIR:-}" "*dev*.json*"   "$DST/biored"
copy_if "${BIORED_SRC_DIR:-}" "*test*.json*"  "$DST/biored"

echo "[DONE] Dataset bootstrap completed. Verify with: scripts/phase7i/verify_splits.py"
