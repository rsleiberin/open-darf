#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT"

echo "--- Phase 7I Doctor ---"

# 1) Env / GPU
echo "[GPU]" && (nvidia-smi --query-gpu=name,memory.total --format=csv,noheader 2>/dev/null || echo "nvidia-smi not available")
echo "[ENV] runner_cmds.env: $( [ -f scripts/phase7i/runner_cmds.env ] && echo PRESENT || echo MISSING )"
if [ -f scripts/phase7i/runner_cmds.env ]; then
  PURE_LINE="$(grep -E '^RUNNER_PURE_CMD=' scripts/phase7i/runner_cmds.env || true)"
  PLM_LINE="$(grep -E '^RUNNER_PLMARKER_CMD=' scripts/phase7i/runner_cmds.env || true)"
  echo "[ENV] $PURE_LINE"
  echo "[ENV] $PLM_LINE"
fi

# 2) Datasets preflight
echo "--- Preflight datasets ---"
bash scripts/phase7i/preflight.sh || { echo "[ERR] Preflight failed"; exit 2; }

# 3) Runner verification (does not require real models to succeed—best effort)
echo "--- Verify runners ---"
if [ -x scripts/phase7i/verify_runners.sh ]; then
  ./scripts/phase7i/verify_runners.sh || true
else
  echo "[WARN] scripts/phase7i/verify_runners.sh not found"
fi

# 4) Latest summary
echo "--- Latest scoreboard summary ---"
SUM="$(ls -1t docs/scoreboards/phase7i/summary_*.md 2>/dev/null | head -n1 || true)"
if [ -n "$SUM" ]; then
  echo "[SUMMARY] $SUM"
  tail -n +1 "$SUM" | sed -n '1,50p'
else
  echo "[SUMMARY] none yet"
fi

# 5) Acceptance snapshot
echo "--- Acceptance snapshot ---"
./scripts/phase7i/acceptance_check.py || true

echo "---------------------------------------"
echo "[DOCTOR] If RUNNER_* point to wrappers with --simulate, acceptance will remain FAIL (expected)."
echo "[NEXT] Edit scripts/phase7i/runner_cmds.env to real commands, then:"
echo "       make runners-verify && make bench-all && make aggregate && make accept && make gate"
