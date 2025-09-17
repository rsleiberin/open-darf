#!/usr/bin/env bash
set -euo pipefail
J_OVERRIDE=""; SHOW_PROGRESS=1
HEARTBEAT_SEC="${PROGRESS_HEARTBEAT_SEC:-2}"
BAR_WIDTH="${PROGRESS_WIDTH:-40}"

log(){ printf "%s\n" "$*" >&2; }

repeat_char() {  # repeat_char <count> <char>
  local n="$1" ch="$2"
  # prints nothing if n<=0 (zero-safe)
  printf '%*s' "$n" '' | tr ' ' "$ch"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -j) J_OVERRIDE="${2:-}"; shift 2;;
    --no-progress) SHOW_PROGRESS=0; shift;;
    -h|--help)
      cat >&2 <<USAGE
ingest_path.sh [-j N] [--no-progress] <dir>
  -j N              number of parallel workers (default: CPU cores, capped)
  --no-progress     disable progress/heartbeat lines (CI-friendly)
env:
  INGEST_CAP                 cap on workers (default 8)
  PROGRESS_HEARTBEAT_SEC     max seconds between prints (default 2)
  PROGRESS_WIDTH             progress bar width (default 40)
USAGE
      exit 0;;
    *) break;;
  esac
done

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
DIR="${1:-}"
[[ -d "$DIR" ]] || { log "[ingest] ERROR: not a directory: $DIR"; exit 2; }

log "[ingest] Step 1/5: Checking CPU core numbers…"
CORES="$(ops/bin/cores.sh 2>/dev/null || echo 1)"
CAP="${INGEST_CAP:-8}"
DEFAULT_J="$CORES"; (( DEFAULT_J > CAP )) && DEFAULT_J="$CAP"
J="${J_OVERRIDE:-${INGEST_WORKERS:-$DEFAULT_J}}"
(( J < 1 )) && J=1
log "[ingest] CPU Cores Found: ${CORES}"
log "[ingest] Workers planned: ${J} (cap=${CAP})"

log "[ingest] Step 2/5: Enumerating files in ${DIR}…"
mapfile -d '' FILES < <(find "$DIR" -type f -not -path '*/.git/*' -not -path "$ROOT/var/manifests/*" -print0 | sort -z)
TOTAL="${#FILES[@]}"
log "[ingest] Files found: ${TOTAL}"

TS="$(date -Is)"
EPOCH="$(date +%s)"
OUT="var/manifests/manifest_${EPOCH}.jsonl"
TMPDIR="$(mktemp -d "var/manifests/.tmp_${EPOCH}_XXXX")"

cleanup() {
  # best-effort stop of monitor
  if [[ -n "${MON_PID:-}" ]]; then kill "$MON_PID" >/dev/null 2>&1 || true; fi
}
trap cleanup EXIT INT TERM

if (( TOTAL == 0 )); then
  : > "$OUT"
  log "[ingest] No files; wrote empty manifest: $OUT"
  echo "$OUT"
  exit 0
fi

log "[ingest] Step 3/5: Launching multi-threaded workers (hash → CAS → JSONL)…"

export ROOT TMPDIR

if (( SHOW_PROGRESS )); then
  log "[ingest] Step 4/5: Progress (updates every ≤${HEARTBEAT_SEC}s)…"
  (
    set +e  # monitor must never die on minor errors
    start="$(date +%s)"; last_print=0; last_done=-1
    # immediate first line @ 0%
    DONE=0
    filled=$(( BAR_WIDTH * DONE / TOTAL )); empty=$(( BAR_WIDTH - filled ))
    printf "[%s%s] %3d%% (%d/%d)  elapsed:%02d:%02d  eta:--:--  phase:hash+CAS\n" \
      "$(repeat_char "$filled" '#')" "$(repeat_char "$empty" '.')" \
      0 0 "$TOTAL" 0 0 >&2

    while :; do
      DONE=$(ls "$TMPDIR"/*.jsonl 2>/dev/null | wc -l | tr -d ' ')
      (( DONE > TOTAL )) && DONE="$TOTAL"
      now="$(date +%s)"; elapsed=$(( now - start ))
      if (( DONE > 0 )); then rate=$(( elapsed * 100 / DONE )); rem=$(( TOTAL - DONE )); eta=$(( (rate*rem)/100 )); else eta=-1; fi
      filled=$(( BAR_WIDTH * DONE / TOTAL )); empty=$(( BAR_WIDTH - filled ))
      if (( (now - last_print) >= HEARTBEAT_SEC || DONE != last_done )); then
        last_print="$now"; last_done="$DONE"
        printf "[%s%s] %3d%% (%d/%d)  elapsed:%02d:%02d  eta:%s  phase:hash+CAS\n" \
          "$(repeat_char "$filled" '#')" "$(repeat_char "$empty" '.')" \
          "$(( 100 * DONE / TOTAL ))" "$DONE" "$TOTAL" \
          "$((elapsed/60))" "$((elapsed%60))" \
          "$([[ $eta -ge 0 ]] && printf "%02d:%02d" $((eta/60)) $((eta%60)) )" >&2
      fi
      (( DONE >= TOTAL )) && break
      sleep 0.2
    done
  ) &
  MON_PID=$!
fi

log "[ingest] Step 5/5: Processing with xargs -P ${J}…"
printf '%s\0' "${FILES[@]}" \
| xargs -0 -n1 -P "$J" bash -c '
  set -euo pipefail
  f="$1"
  out="$(mktemp -p "$TMPDIR" tmp.XXXXXX.jsonl)"
  ${WORKER_BIN:-ops/bin/_ingest_worker2.sh} "$ROOT" "$f" > "$out" 2>>"$TMPDIR/errs.log"
' _

# let monitor finish its final tick
if (( SHOW_PROGRESS )) && [[ -n "${MON_PID:-}" ]]; then
  wait "$MON_PID" 2>/dev/null || true
fi

LC_ALL=C sort -t '"' -k4,4 "$TMPDIR"/*.jsonl > "$OUT"
COUNT="$(wc -l < "$OUT" | tr -d ' ')"
log "[ingest] Completed: wrote manifest $OUT ($COUNT files) at $TS"
echo "$OUT"
