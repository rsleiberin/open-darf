#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
DATA="$ROOT/data"

fail(){ echo "[PREFLIGHT][FAIL] $*"; exit 2; }
ok(){ echo "[PREFLIGHT][OK] $*"; }

check_ds(){
  local ds="$1"
  local base="$DATA/$ds"
  [ -d "$base" ] || fail "dataset dir missing: $base"
  local bad=0
  for sp in train dev test; do
    local f_jsonl="$base/$sp.jsonl"
    local f_json="$base/$sp.json"
    local f=""
    if [ -f "$f_jsonl" ]; then f="$f_jsonl"; elif [ -f "$f_json" ]; then f="$f_json"; fi
    [ -n "$f" ] || { echo "[PREFLIGHT] $ds/$sp missing"; bad=$((bad+1)); continue; }
    local lines
    if head -c 1 "$f" >/dev/null 2>&1; then
      # count lines for JSONL; for JSON array, treat non-empty as >=1
      if grep -q '^{\|}\|^\[' "$f"; then
        # heuristics: if starts with '[', assume >=1 when file size > 2 bytes
        if head -c 1 "$f" | grep -q '\['; then
          lines=$( [ $(stat -c%s "$f" 2>/dev/null || wc -c < "$f") -gt 2 ] && echo 1 || echo 0 )
        else
          # JSONL fallback count
          lines=$(wc -l < "$f" | tr -d ' ')
        fi
      else
        lines=$(wc -l < "$f" | tr -d ' ')
      fi
    else
      lines=0
    fi
    if [ "$lines" -gt 0 ]; then
      echo "[PREFLIGHT] $ds/$sp OK (lines=$lines) file=$f"
    else
      echo "[PREFLIGHT] $ds/$sp EMPTY (lines=0) file=$f"
      bad=$((bad+1))
    fi
  done
  [ "$bad" -eq 0 ] || fail "$ds has $bad split issues"
}

check_ds scierc
check_ds biored
ok "datasets look usable"
