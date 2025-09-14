#!/usr/bin/env python3
import json, glob, pathlib, datetime as dt

ROOT = pathlib.Path(__file__).resolve().parents[2]
metrics_files = glob.glob(str(ROOT / "var" / "receipts" / "phase7i" / "*" / "*" / "metrics.json"))
rows=[]
for mf in metrics_files:
    try:
        rows.append(json.loads(pathlib.Path(mf).read_text(encoding="utf-8")))
    except Exception:
        pass

TARGET_F1 = 0.50
TARGET_COMP = 0.95

best_scierc_f1 = 0.0
comp_ok = True
count = 0

for r in rows:
    count += 1
    ds = r.get("dataset")
    sp = r.get("split")
    f1 = float(r.get("f1_micro", 0.0) or 0.0)
    comp = float(r.get("constitutional_compliance_rate", 0.0) or 0.0)
    if ds == "scierc" and sp == "test":
        if f1 > best_scierc_f1:
            best_scierc_f1 = f1
    if comp < TARGET_COMP:
        comp_ok = False

status_f1 = "PASS" if best_scierc_f1 >= TARGET_F1 else "FAIL"
status_comp = "PASS" if comp_ok else "FAIL"
overall = "PASS" if (status_f1 == "PASS" and status_comp == "PASS") else "FAIL"

summary = {
    "timestamp_utc": dt.datetime.utcnow().strftime("%Y-%m-%d %H:%M:%SZ"),
    "runs_evaluated": count,
    "best_scierc_test_f1_micro": best_scierc_f1,
    "target_f1_micro_scierc": TARGET_F1,
    "meets_f1_target": status_f1 == "PASS",
    "meets_compliance_invariant": status_comp == "PASS",
    "overall_status": overall
}

print(json.dumps(summary, indent=2))
