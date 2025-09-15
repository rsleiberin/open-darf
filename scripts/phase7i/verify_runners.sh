#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
ENV_FILE="$ROOT/scripts/phase7i/runner_cmds.env"

info(){ echo "[RUNNER][INFO] $*"; }
ok(){ echo "[RUNNER][OK] $*"; }
fail(){ echo "[RUNNER][FAIL] $*"; exit 2; }

[ -f "$ENV_FILE" ] || fail "Missing $ENV_FILE — please create and set RUNNER_PURE_CMD and RUNNER_PLMARKER_CMD."

# shellcheck disable=SC1090
. "$ENV_FILE"

[ -n "${RUNNER_PURE_CMD:-}" ] || fail "RUNNER_PURE_CMD not set in runner_cmds.env"
[ -n "${RUNNER_PLMARKER_CMD:-}" ] || fail "RUNNER_PLMARKER_CMD not set in runner_cmds.env"

# Resolve first word as binary for existence check
BIN_PURE="$(echo "$RUNNER_PURE_CMD" | awk '{print $1}')"
BIN_PLM="$(echo "$RUNNER_PLMARKER_CMD" | awk '{print $1}')"

command -v "$BIN_PURE" >/dev/null 2>&1 || fail "Binary not found for RUNNER_PURE_CMD: $BIN_PURE"
command -v "$BIN_PLM"  >/dev/null 2>&1 || fail "Binary not found for RUNNER_PLMARKER_CMD: $BIN_PLM"

info "Probing --help (best effort; tolerated if non-zero)"
set +e
$RUNNER_PURE_CMD --help >/dev/null 2>&1
PURE_RC=$?
$RUNNER_PLMARKER_CMD --help >/dev/null 2>&1
PLM_RC=$?
set -e

ok "Resolved binaries. PURE(--help rc=$PURE_RC) PL-Marker(--help rc=$PLM_RC)"

# CUDA/GPU quick probe
if command -v nvidia-smi >/dev/null 2>&1; then
  MEM_FREE="$(nvidia-smi --query-gpu=memory.free --format=csv,noheader,nounits 2>/dev/null | head -n1 || echo "")"
  info "GPU available. Free VRAM ~ ${MEM_FREE} MiB"
else
  info "nvidia-smi not found; GPU metrics will be skipped."
fi

ok "Runner verification passed."
