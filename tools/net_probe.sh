#!/usr/bin/env bash
set -euo pipefail

TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUTDIR="var/receipts/${TS}_net_probe"
mkdir -p "$OUTDIR"

echo "[net] BEGIN → $OUTDIR"
echo "[sys] resolv.conf:" | tee "$OUTDIR/net_probe.out"
sed -n '1,80p' /etc/resolv.conf 2>/dev/null | tee -a "$OUTDIR/net_probe.out" || true

# Helper: probe a single host
probe_host () {
  local host="$1"
  echo "[host] $host" | tee -a "$OUTDIR/net_probe.out"
  # DNS via getent (glibc resolver)
  if getent hosts "$host" >/dev/null 2>&1; then
    echo "  [dns] getent: OK $(getent hosts "$host" | head -n1)" | tee -a "$OUTDIR/net_probe.out"
  else
    echo "  [dns] getent: FAIL" | tee -a "$OUTDIR/net_probe.out"
  fi
  # ICMP ping (may be blocked; non-fatal)
  if ping -c1 -W1 "$host" >/dev/null 2>&1; then
    echo "  [ping] 1/1 OK" | tee -a "$OUTDIR/net_probe.out"
  else
    echo "  [ping] timeout/blocked" | tee -a "$OUTDIR/net_probe.out"
  fi
  # HTTP HEAD with curl if available
  if command -v curl >/dev/null 2>&1; then
    local t0 t1 dt
    t0=$(date +%s%3N)
    if curl -I -sS --max-time 8 "https://$host/" | head -n1 | tee -a "$OUTDIR/net_probe.out"; then
      t1=$(date +%s%3N); dt=$((t1 - t0))
      echo "  [http] HEAD ok ~${dt}ms" | tee -a "$OUTDIR/net_probe.out"
    else
      echo "  [http] HEAD failed" | tee -a "$OUTDIR/net_probe.out"
    fi
  else
    echo "  [http] curl not installed" | tee -a "$OUTDIR/net_probe.out"
  fi
}

probe_host "pypi.org"
probe_host "download.pytorch.org"
probe_host "github.com"

echo "0" > "$OUTDIR/net_probe.rc"
echo "[net] END rc=0"
