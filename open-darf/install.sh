#!/usr/bin/env bash
set -euo pipefail

echo "[install] probing environment…"
DISTRO="$( (lsb_release -ds 2>/dev/null || grep -m1 PRETTY_NAME /etc/os-release | cut -d= -f2 | tr -d '"') || echo unknown )"
UBU_VER="$( (lsb_release -rs 2>/dev/null) || echo "" )"
KREL="$(uname -r || echo unknown)"
IS_WSL=0
if echo "$KREL" | grep -qi microsoft; then IS_WSL=1; fi
if [[ -n "${WSL_INTEROP:-}" ]]; then IS_WSL=1; fi
REQS_OK=1

echo "[install] distro: $DISTRO"
echo "[install] kernel: $KREL"
echo "[install] wsl   : $IS_WSL"

if ! command -v python3 >/dev/null 2>&1; then
  echo "[install:error] python3 missing"; REQS_OK=0
fi
if ! command -v git >/dev/null 2>&1; then
  echo "[install:error] git missing"; REQS_OK=0
fi
if command -v nvidia-smi >/dev/null 2>&1; then
  echo "[install] nvidia-smi present: $(nvidia-smi --query-gpu=name,driver_version --format=csv,noheader 2>/dev/null | tr '\n' ';')"
else
  echo "[install:warn] nvidia-smi not found; GPU validation will be skipped"
fi

GPU_REQ_NOTE="native Ubuntu 22.04 LTS + RTX 30/40 recommended for GPU runs"
if [[ "$UBU_VER" != "22.04" && "$DISTRO" != *"22.04"* ]]; then
  echo "[install:warn] not Ubuntu 22.04; $GPU_REQ_NOTE"
fi
if [[ $IS_WSL -eq 1 ]]; then
  echo "[install:warn] WSL detected; GPU validation may be blocked. $GPU_REQ_NOTE"
fi

if [[ $REQS_OK -ne 1 ]]; then
  echo "[install] requirements NOT met"
  exit 2
fi

echo "[install] ok"
exit 0
