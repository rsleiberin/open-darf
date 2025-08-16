#!/usr/bin/env bash
set -Eeuo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TLA_DIR="$ROOT/verification/tla"
CFG_DIR="classA_cfgs"
SPEC_DIR="classA_specs"
RUN_DIR="$TLA_DIR/runs"
JAR="${TLA_JAR:-$TLA_DIR/tools/tla2tools.jar}"
WORKERS="${WORKERS:-4}"

run_tlc() {
  if command -v tlc >/dev/null 2>&1; then tlc -workers "$WORKERS" "$@"
  elif [[ -f "$JAR" ]]; then java -XX:+UseParallelGC -XX:ActiveProcessorCount="$WORKERS" -cp "$JAR" tlc2.TLC -tool "$@"
  else echo "[ERR] TLC not found (tlc or $JAR)"; exit 127; fi
}

mkdir -p "$RUN_DIR"
summary=()
pushd "$TLA_DIR" >/dev/null
shopt -s nullglob
for cfg in "$CFG_DIR"/*_pos.cfg "$CFG_DIR"/*_neg.cfg; do
  [[ -e "$cfg" ]] || continue
  base="$(basename "$cfg")"
  kind="${base##*_}"; kind="${kind%.cfg}"
  mod="${base%_${kind}.cfg}"
  tla="$SPEC_DIR/$mod.tla"
  [[ -f "$tla" ]] || { echo "[ERR] missing $tla"; summary+=("$mod,$kind,FAIL,NO-SPEC"); continue; }
  out="$RUN_DIR/$mod"; mkdir -p "$out"
  stamp="$(date +%Y%m%d-%H%M%S)"
  log="$out/${mod}_${kind}_${stamp}.log"
  mdir="$out/states_${stamp}_${kind}"
  set +e
  run_tlc -deadlock -metadir "$mdir" -config "$cfg" "$tla" >"$log" 2>&1
  rc=$?
  set -e
  if [[ "$kind" == "pos" ]]; then
    if [[ $rc -eq 0 ]] && grep -q "No error has been found" "$log"; then
      echo "[OK ] $mod ($kind)"; summary+=("$mod,$kind,PASS,$log")
    else
      echo "[ERR] $mod ($kind) failed. See $log"; summary+=("$mod,$kind,FAIL,$log")
    fi
  else
    if grep -Eiq "Error:|Invariant .* is violated" "$log"; then
      echo "[BITE] $mod ($kind)"; summary+=("$mod,$kind,BITE,$log")
    else
      echo "[ERR ] $mod ($kind) no bite. See $log"; summary+=("$mod,$kind,NO-BITE,$log")
    fi
  fi
done
popd >/dev/null

echo; printf "%-28s %-6s %-8s %s\n" "MODULE" "KIND" "RESULT" "LOG"
for row in "${summary[@]}"; do IFS=',' read -r m k r l <<<"$row"; printf "%-28s %-6s %-8s %s\n" "$m" "$k" "$r" "$l"; done
