#!/usr/bin/env python3
"""
Runs the stdlib heuristic baseline on SciERC dev and asserts F1 >= 0.20.
Outputs a compact JSON receipt.
"""
import json, os, subprocess, time, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]
runroot = ROOT / "var" / "receipts" / "phase7g" / "relex_ci_smoke" / time.strftime("%Y%m%d-%H%M%S")
runroot.mkdir(parents=True, exist_ok=True)

cmd = ["python3", str(ROOT/"apps/relex/baseline.py"),
       "--dataset_dir", "data/scierc_norm",
       "--split", "dev",
       "--outdir", str(runroot)]
p = subprocess.run(cmd, capture_output=True, text=True)
rc = p.returncode

metrics_path = runroot / "metrics.json"
result = {"status":"error","rc":rc,"stdout":p.stdout[-4000:],"stderr":p.stderr[-4000:]}

if rc==0 and metrics_path.exists():
    m = json.loads(metrics_path.read_text())
    f1 = m.get("f1_micro", 0.0)
    comp = m.get("constitutional_compliance_rate", 1.0)
    passed = (f1 >= 0.20) and (comp >= 0.95)
    result = {
        "status":"ok" if passed else "fail",
        "f1_micro": f1,
        "precision_micro": m.get("precision_micro"),
        "recall_micro": m.get("recall_micro"),
        "pred": m.get("pred_count"), "gold": m.get("gold_pairs"),
        "receipt_dir": str(runroot), "constitutional_compliance_rate": comp
    }
    print(json.dumps(result, indent=2))
    sys.exit(0 if passed else 1)
else:
    print(json.dumps(result, indent=2))
    sys.exit(1)
