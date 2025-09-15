#!/usr/bin/env bash
set -euo pipefail
printf "===\n===\n===\n"
echo "[finalize] aggregate → timing → package → FINAL_REPORT.md"

# 1) Aggregate evidence
./scripts/phase7s/aggregate_evidence.sh || true

# 2) Extract timing summaries
scripts/phase7s/extract_timing_from_tarballs.py || true

# 3) Package evidence
./scripts/phase7s/package_evidence.sh || true

# 4) Build FINAL_REPORT.md from JSON summaries (best-effort)
TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
OUT_MD="docs/phase7s/FINAL_REPORT.md"
VAL_JSON="var/reports/phase7s/validation_summary.json"
TIM_JSON="var/reports/phase7s/timing_summary.json"
BUNDLE="$(ls -1t var/reports/phase7s/phase7s_evidence_bundle_*.tar.gz 2>/dev/null | head -n1 || true)"
MANIFEST="$(ls -1t var/reports/phase7s/MANIFEST_*.txt 2>/dev/null | head -n1 || true)"
B_SHA=""; B_SIZE=""
if [[ -f "$BUNDLE" ]]; then
  B_SHA="$(sha256sum "$BUNDLE" | awk '{print $1}')"
  B_SIZE="$(stat -c %s "$BUNDLE" 2>/dev/null || echo "")"
fi

python3 - "$TS" "$VAL_JSON" "$TIM_JSON" "$OUT_MD" "$BUNDLE" "$MANIFEST" "$B_SHA" "$B_SIZE" << 'PY'
import json, sys, os, datetime
ts, valp, timp, outp, bundle, manifest, bsha, bsize = sys.argv[1:]
val = {}
tim = {}
try:
    with open(valp, "r", encoding="utf-8") as f: val = json.load(f)
except Exception: val = {}
try:
    with open(timp, "r", encoding="utf-8") as f: tim = json.load(f)
except Exception: tim = {}

def get(d, path, default="n/a"):
    cur = d
    for k in path.split("."):
        if not isinstance(cur, dict) or k not in cur: return default
        cur = cur[k]
    return cur

receipts = get(val, "receipts.count", 0)
wsl = get(val, "receipts.by_wsl.wsl", 0)
native = get(val, "receipts.by_wsl.native", 0)
install = get(val, "receipts.install_ok", 0)
runmin = get(val, "receipts.run_minimal_ok", 0)
evid = get(val, "receipts.evidence_ok", 0)

def ci_str(ci):
    if not isinstance(ci, dict) or ci.get("p") is None: return "n/a"
    return f"{ci['p']*100:.1f}% (95% CI {ci['lo']*100:.1f}–{ci['hi']*100:.1f}%)"

ci_install = ci_str(get(val, "receipts.install_ok_ci95", {}))
ci_runmin = ci_str(get(val, "receipts.run_minimal_ok_ci95", {}))
ci_evid   = ci_str(get(val, "receipts.evidence_ok_ci95", {}))

tim_samp = tim.get("samples", 0)
tim_ci = tim.get("sub_ms", {}).get("ci95", {})
tim_ratio = ci_str(tim_ci)

lines = []
lines.append("# Phase 7S — FINAL REPORT")
lines.append("")
lines.append(f"- Generated: {ts}")
lines.append("")
lines.append("## Evidence Summary")
lines.append(f"- Receipts: {receipts}  (WSL:{wsl} · Native:{native})")
lines.append(f"- Install success: {install} — {ci_install}")
lines.append(f"- Minimal run success: {runmin} — {ci_runmin}")
lines.append(f"- Evidence packaging success: {evid} — {ci_evid}")
lines.append("")
lines.append("## Timing Probe")
lines.append(f"- Samples with timing_probe.json: {tim_samp}")
lines.append(f"- Sub-ms support ratio: {tim_ratio}")
lines.append("")
lines.append("## Bundle & Manifest")
lines.append(f"- Bundle: {bundle or 'n/a'}")
lines.append(f"- Manifest: {manifest or 'n/a'}")
lines.append(f"- sha256: {bsha or 'n/a'}")
lines.append(f"- size (bytes): {bsize or 'n/a'}")
lines.append("")
lines.append("## Quick Links (paths)")
lines.append("- docs/phase7s/INDEX.md")
lines.append("- var/reports/phase7s/validation_summary.{json,md}")
lines.append("- var/reports/phase7s/timing_summary.{json,md}")
lines.append("- open-darf/var/receipts/open-darf/")
lines.append("- var/receipts/community/")
with open(outp, "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
print(f"[report] wrote {outp}")
PY

echo "[finalize] done"
