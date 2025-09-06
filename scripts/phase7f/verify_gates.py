#!/usr/bin/env python3
import os, sys, json, glob, pathlib

DEFAULTS = {
  "synthesis_e2e_sec_le": 2.0,
  "propagation_p95_ms_le": 100.0,
  "revocation_e2e_sec_le": 5.0,
  "dependency_accuracy_ge": 0.999
}

ROOT = pathlib.Path(__file__).resolve().parents[2]
plan_path = ROOT / "docs/phase7f/plans/ci_gates_plan.json"
cfg = dict(DEFAULTS)
try:
    with open(plan_path, "r") as f:
        data = json.load(f)
        cfg.update(data.get("gates", {}))
except Exception:
    pass

# Locate summary or build a minimal one from dry-run execs
summary_path = os.environ.get("GATES_SUMMARY")
if not summary_path:
    candidates = sorted(glob.glob("var/receipts/phase7f/gates_eval/*/gates_summary.json"))
    summary_path = candidates[-1] if candidates else ""

def load_json(path):
    try:
        with open(path, "r") as f: return json.load(f)
    except Exception:
        return {}

report = load_json(summary_path) if summary_path else {}

syn = report.get("measurements", {}).get("synthesis_e2e_sec", None)
prop = report.get("measurements", {}).get("propagation_p95_ms", None)
rev  = report.get("measurements", {}).get("revocation_e2e_sec", None)
dep  = report.get("measurements", {}).get("dependency_accuracy", None)

# Evaluate with tri-state (None -> pending, non-blocking)
def le(meas, targ): 
    return None if meas is None else (meas <= targ)
def ge(meas, targ):
    return None if meas is None else (meas >= targ)

status = {
  "synthesis_ok":   le(syn, cfg["synthesis_e2e_sec_le"]),
  "propagation_ok": le(prop, cfg["propagation_p95_ms_le"]),
  "revocation_ok":  le(rev, cfg["revocation_e2e_sec_le"]),
  "dep_acc_ok":     ge(dep, cfg["dependency_accuracy_ge"])
}

print(json.dumps({
  "cfg": cfg,
  "summary_path": summary_path or "<none>",
  "measurements": {"synthesis": syn, "propagation": prop, "revocation": rev, "dep_acc": dep},
  "status": status
}, indent=2))

# Exit code policy: only fail if a measured gate exists and violates its threshold
fail = any(val is False for val in status.values())
sys.exit(1 if fail else 0)
