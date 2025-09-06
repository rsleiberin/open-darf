#!/usr/bin/env python3
import os, json, glob, subprocess, time

TARGETS = {
  "synthesis_e2e_sec_le": 2.0,
  "propagation_p95_ms_le": 100.0,
  "revocation_e2e_sec_le": 5.0,
  "dependency_accuracy_ge": 0.999
}

def git_head_short():
    try: return subprocess.check_output(["git","rev-parse","--short=12","HEAD"], text=True).strip()
    except Exception: return "unknown"

def latest(globpat):
    paths = sorted(glob.glob(globpat), key=os.path.getmtime, reverse=True)
    return paths[0] if paths else None

def load_json(path):
    with open(path) as f: return json.load(f)

def main():
    head = git_head_short()
    synth = latest("var/receipts/phase7f/dryrun_exec/*/synthesis_exec.json")
    revo  = latest("var/receipts/phase7f/dryrun_exec/*/revocation_exec.json")
    prop  = latest("var/receipts/phase7f/propagation_perf/*/summary.json")
    depm  = latest("var/receipts/phase7f/dep_acc/*/metrics.json")

    measurements = { "synthesis_e2e_sec": None, "propagation_p95_ms": None, "revocation_e2e_sec": None, "dependency_accuracy": None }

    try:
        if synth: measurements["synthesis_e2e_sec"] = float(load_json(synth).get("timing_sec"))
        if revo:  measurements["revocation_e2e_sec"] = float(load_json(revo).get("timing_sec"))
        if prop:  measurements["propagation_p95_ms"] = float(load_json(prop)["summary"]["p95_ms"])
        if depm:  measurements["dependency_accuracy"] = float(load_json(depm)["micro"]["recall"])
    except Exception:
        pass

    status = {
      "synthesis_ok": None if measurements["synthesis_e2e_sec"] is None else measurements["synthesis_e2e_sec"] <= TARGETS["synthesis_e2e_sec_le"],
      "propagation_ok": None if measurements["propagation_p95_ms"] is None else measurements["propagation_p95_ms"] <= TARGETS["propagation_p95_ms_le"],
      "revocation_ok": None if measurements["revocation_e2e_sec"] is None else measurements["revocation_e2e_sec"] <= TARGETS["revocation_e2e_sec_le"],
      "dep_acc_ok": None if measurements["dependency_accuracy"] is None else measurements["dependency_accuracy"] >= TARGETS["dependency_accuracy_ge"]
    }

    out = { "phase":"7F", "head":head, "targets":TARGETS, "measurements":measurements, "status":status }
    ts = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir = f"var/receipts/phase7f/gates_eval/{ts}"
    os.makedirs(outdir, exist_ok=True)
    path = os.path.join(outdir, "gates_summary.json")
    with open(path, "w") as f: json.dump(out, f, indent=2)
    print(path)
if __name__ == "__main__":
    main()
