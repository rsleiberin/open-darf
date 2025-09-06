#!/usr/bin/env python3
from __future__ import annotations
import os, glob, json, time, pathlib, statistics

def latest(globpat):
    paths = sorted(glob.glob(globpat), key=os.path.getmtime, reverse=True)
    return paths[0] if paths else None

def load_json(p, default=None):
    try:
        with open(p) as f: return json.load(f)
    except Exception:
        return default

def main():
    ts=time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir=f"var/receipts/phase7f/e2e/{ts}"
    pathlib.Path(outdir).mkdir(parents=True, exist_ok=True)

    fused = latest("var/receipts/phase7f/orchestrator_run/*/fused.json")
    prop  = latest("var/receipts/phase7f/propagation_perf/*/summary.json")
    dep   = latest("var/receipts/phase7f/dep_acc/*/metrics.json")
    rev_plan = latest("var/receipts/phase7f/revocation_demo/*/revocation_plan.json")
    rev_commit = latest("var/receipts/phase7f/revocation_commit/*/commit_receipt.json")
    gates = latest("var/receipts/phase7f/gates_eval/*/gates_summary.json")

    p95_ms = None
    if prop:
        pj = load_json(prop, {})
        # accept common shapes
        p95_ms = pj.get("summary", {}).get("p95_ms")
        if p95_ms is None: p95_ms = pj.get("p95_ms")

    synthesis_e2e = None
    revocation_e2e = None
    if gates:
        gj = load_json(gates, {})
        m = gj.get("measurements", {})
        synthesis_e2e = m.get("synthesis_e2e_sec")
        revocation_e2e = m.get("revocation_e2e_sec")

    dep_acc = None
    if dep:
        dj = load_json(dep, {})
        dep_acc = dj.get("dependency_accuracy") or dj.get("accuracy")

    scope = []
    if rev_plan:
        rj = load_json(rev_plan, {})
        scope = rj.get("cascade_scope_sorted", []) or []

    budgets = {
        "synthesis_e2e_sec_le": 2.0,
        "propagation_p95_ms_le": 100.0,
        "revocation_e2e_sec_le": 5.0,
        "dependency_accuracy_ge": 0.999
    }
    status = {
        "synthesis_ok": (synthesis_e2e is not None and synthesis_e2e <= budgets["synthesis_e2e_sec_le"]),
        "propagation_ok": (p95_ms is not None and p95_ms <= budgets["propagation_p95_ms_le"]),
        "revocation_ok": (revocation_e2e is not None and revocation_e2e <= budgets["revocation_e2e_sec_le"]),
        "dep_acc_ok": (dep_acc is not None and dep_acc >= budgets["dependency_accuracy_ge"]),
    }

    out = {
        "phase":"7F",
        "generated_at_utc": ts,
        "inputs": {
            "fused_json": fused, "propagation_summary": prop, "dep_acc": dep,
            "revocation_plan": rev_plan, "revocation_commit": rev_commit, "gates": gates
        },
        "measurements": {
            "synthesis_e2e_sec": synthesis_e2e,
            "propagation_p95_ms": p95_ms,
            "revocation_e2e_sec": revocation_e2e,
            "dependency_accuracy": dep_acc
        },
        "budgets": budgets,
        "status": status,
        "revocation_scope_sample": scope[:8]
    }
    with open(f"{outdir}/summary.json","w") as f: json.dump(out,f,indent=2)
    print(f"{outdir}/summary.json", end="")

if __name__ == "__main__":
    main()
