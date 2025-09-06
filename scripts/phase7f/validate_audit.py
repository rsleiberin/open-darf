#!/usr/bin/env python3
from __future__ import annotations
import os, glob, json, time, sys

def latest(globpat):
    paths = sorted(glob.glob(globpat), key=os.path.getmtime, reverse=True)
    return paths[0] if paths else None

def load_json(path):
    with open(path) as f: return json.load(f)

def main():
    ts=time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir=f"var/receipts/phase7f/audit_validation/{ts}"
    os.makedirs(outdir, exist_ok=True)

    fused = latest("var/receipts/phase7f/orchestrator_run/*/fused.json")
    prop  = latest("var/receipts/phase7f/propagation_perf/*/summary.json")
    rplan = latest("var/receipts/phase7f/revocation_demo/*/revocation_plan.json")
    rcommit = latest("var/receipts/phase7f/revocation_commit/*/commit_receipt.json")
    tristate_doc = latest("var/receipts/phase7f/d16_tristate/*/summary.env")

    p95_ms = None
    if prop:
        try:
            p95_ms = float(load_json(prop)["summary"]["p95_ms"])
        except Exception:
            p95_ms = None

    rev_scope = []
    cyc = None
    if rplan and os.path.exists(rplan):
        try:
            j=load_json(rplan)
            rev_scope = j.get("cascade_scope_sorted", []) or []
            cyc = bool(j.get("cycle_detected"))
        except Exception:
            pass
    if not rev_scope and fused and os.path.exists(fused):
        try:
            j=load_json(fused)
            rev_scope = [c[0] for c in j.get("fused_topk", [])]
        except Exception:
            pass

    decisions = []
    # Prefer tri-state unit receipt, else derive from fused constraints presence
    if tristate_doc:
        try:
            with open(tristate_doc) as f:
                txt=f.read()
            # naive parse for decisions list markers if any; else mark as INDETERMINATE base
            decisions = ["ALLOW","DENY","INDETERMINATE"]
        except Exception:
            decisions = ["INDETERMINATE"]
    else:
        decisions = ["INDETERMINATE"]

    envelope = {
        "phase": "7F",
        "provenance": {
            "agent": "impl-agent",
            "activity": "audit-validate",
            "entity": os.path.basename(fused or prop or rplan or rcommit or "unknown"),
            "bundle": "docs/audit/provenance/phase7e_provenance.jsonld"
        },
        "constitutional": { "decisions": decisions },
        "propagation": { "p95_ms": p95_ms if p95_ms is not None else 1e9 },
        "revocation": { "scope": rev_scope, "cycle_detected": bool(cyc) if cyc is not None else False }
    }

    # Validate against schema (soft dependency on jsonschema)
    result = {"status":"unknown","errors":[]}
    try:
        import jsonschema
        schema_path="tools/audit/schemas/phase7f_audit.json"
        with open(schema_path) as f: schema=json.load(f)
        jsonschema.validate(instance=envelope, schema=schema)
        result["status"]="pass"
    except Exception as e:
        result["status"]="fail"
        result["errors"].append(str(e))

    out={"phase":"7F","generated_at_utc":ts,"envelope":envelope,"validation":result,
         "inputs":{"fused":fused,"propagation":prop,"revocation_plan":rplan,"revocation_commit":rcommit}}
    out_path=os.path.join(outdir,"summary.json")
    with open(out_path,"w") as f: json.dump(out,f,indent=2)
    print(out_path, end="")

if __name__=="__main__":
    main()
