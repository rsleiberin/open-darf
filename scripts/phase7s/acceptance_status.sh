#!/usr/bin/env bash
set -euo pipefail

TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUTDIR="var/reports/phase7s"
JSON="$OUTDIR/acceptance_status_${TS}.json"
MD="$OUTDIR/acceptance_status_${TS}.md"
mkdir -p "$OUTDIR"

VAL_JSON="$OUTDIR/validation_summary.json"
TIM_JSON="$OUTDIR/timing_summary.json"

LATEST_BUNDLE="$(ls -1t "$OUTDIR"/phase7s_evidence_bundle_*.tar.gz 2>/dev/null | head -n1 || true)"
LATEST_MANIFEST="$(ls -1t "$OUTDIR"/MANIFEST_*.txt 2>/dev/null | head -n1 || true)"

python3 - "$TS" "$VAL_JSON" "$TIM_JSON" "$JSON" "$MD" "$LATEST_BUNDLE" "$LATEST_MANIFEST" << 'PY'
import json, glob, os, sys

TS, VAL, TIM, OUT_JSON, OUT_MD, BUNDLE, MANIFEST = sys.argv[1:]

def read_json(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}

val = read_json(VAL)
tim = read_json(TIM)

def state(ok=None, reason=""):
    if ok is True: return {"state":"ALLOW","reason":reason}
    if ok is False: return {"state":"DENY","reason":reason}
    return {"state":"INDETERMINATE","reason":reason}

# Discover receipts
oneclick = sorted(glob.glob("open-darf/var/receipts/open-darf/oneclick_*.json"))
native_checks = sorted(glob.glob("var/receipts/phase7s/native_check_*.json"))

def read(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            j = json.load(f)
            j["_path"]=path
            return j
    except Exception as e:
        return {"_path":path, "_error":str(e)}

oneclick_j = [read(p) for p in oneclick]
native_j = [read(p) for p in native_checks]

# Metrics from summaries
val_receipts = int(val.get("receipts", {}).get("count", 0) or 0)
evidence_ok = int(val.get("receipts", {}).get("evidence_ok", 0) or 0)
tim_samples = int(tim.get("samples", 0) or 0)

# Native signal present?
has_native_gate_pass = any((j.get("gate",{}).get("passed")==1) for j in native_j)
has_nonwsl_oneclick = any((j.get("is_wsl")==0 and j.get("steps",{}).get("run_minimal_rc")==0 and j.get("steps",{}).get("evidence_rc")==0) for j in oneclick_j)
native_ok = has_native_gate_pass or has_nonwsl_oneclick

# Repo docs presence
repo_docs_ok = all(os.path.isfile(p) for p in [
    "docs/architecture/branch_consolidation_plan.md",
    "docs/architecture/post_grant_integration_roadmap.md"
])

# Bundle presence
bundle_ok = bool(BUNDLE) and os.path.isfile(BUNDLE) and bool(MANIFEST) and os.path.isfile(MANIFEST)

report = {
  "timestamp": TS,
  "criteria": {
    "C1_repo_consolidation_docs": state(repo_docs_ok, "branch_consolidation_plan.md & post_grant_integration_roadmap.md"),
    "C2_validation_flow_operational": state(val_receipts>0 and evidence_ok>0, f"receipts={val_receipts}, evidence_ok={evidence_ok}"),
    "C3_timing_probe_integrated": state(tim_samples>0, f"samples_with_timing={tim_samples}"),
    "C4_evidence_bundle_ready": state(bundle_ok, f"bundle={'present' if bundle_ok else 'missing'}"),
    "C5_native_ubuntu_gpu_evidence": state(True if native_ok else False if (oneclick_j or native_j) else None,
                                          "pass if native gate passed or non-WSL oneclick with run+evidence OK"),
  },
  "artifacts": {
    "validation_summary_json": VAL,
    "timing_summary_json": TIM,
    "evidence_bundle": BUNDLE or "",
    "manifest": MANIFEST or "",
    "oneclick_receipts": [j.get("_path") for j in oneclick_j][-5:],
    "native_gate_receipts": [j.get("_path") for j in native_j][-5:]
  }
}

with open(OUT_JSON, "w", encoding="utf-8") as f: json.dump(report, f, indent=2)

md = []
md.append("# Phase 7S — Acceptance Status\n")
md.append(f"- Generated: {TS}\n")
for key, item in report["criteria"].items():
    md.append(f"- {key}: {item['state']} — {item['reason']}")
md.append("\n## Artifacts\n")
md.append(f"- validation_summary.json: {VAL}")
md.append(f"- timing_summary.json: {TIM}")
md.append(f"- bundle: {BUNDLE or 'n/a'}")
md.append(f"- manifest: {MANIFEST or 'n/a'}")
if report["artifacts"]["oneclick_receipts"]:
    md.append("- sample oneclick receipts:")
    for p in report["artifacts"]["oneclick_receipts"]:
        md.append(f"  - {p}")
if report["artifacts"]["native_gate_receipts"]:
    md.append("- native gate receipts:")
    for p in report["artifacts"]["native_gate_receipts"]:
        md.append(f"  - {p}")

with open(OUT_MD, "w", encoding="utf-8") as f:
    f.write("\n".join(md) + "\n")

print("[ok] wrote", OUT_JSON, "and", OUT_MD)
PY
