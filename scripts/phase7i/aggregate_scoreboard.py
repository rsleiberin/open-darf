#!/usr/bin/env python3
import json, glob, hashlib, datetime as dt, pathlib, sys
from collections import defaultdict

ROOT = pathlib.Path(__file__).resolve().parents[2]
schema_path = ROOT / "docs" / "schemas" / "metrics_v1.json"
rows = []
for mf in glob.glob(str(ROOT / "var" / "receipts" / "phase7i" / "*" / "*" / "metrics.json")):
    try:
        data = json.loads(pathlib.Path(mf).read_text(encoding="utf-8"))
        rows.append(data)
    except Exception:
        pass

def md_table(rows):
    hdr = ["dataset","split","model","precision_micro","recall_micro","f1_micro","f1_unlabeled","pred_count","gold_pairs","latency_ms","constitutional_compliance_rate"]
    out = ["|"+"|".join(hdr)+"|", "|"+"|".join(["---"]*len(hdr))+"|"]
    for r in rows:
        out.append("|"+"|".join(str(r.get(k,"")) for k in hdr)+"|")
    return "\n".join(out)

def assess(rows):
    # Targets
    target = {"dataset":"scierc","split":"test","f1_micro":0.50,"compliance":0.95}
    meet = {"f1": False, "comp": True}
    best_f1 = 0.0
    for r in rows:
        if r.get("dataset")=="scierc" and r.get("split")=="test":
            f1 = float(r.get("f1_micro",0.0) or 0.0)
            best_f1 = max(best_f1, f1)
            comp = float(r.get("constitutional_compliance_rate",0.0) or 0.0)
            if comp < target["compliance"]:
                meet["comp"] = False
    meet["f1"] = best_f1 >= target["f1_micro"]
    return target, meet, best_f1

ts = dt.datetime.utcnow().strftime("%Y-%m-%d %H:%M:%SZ")
target, meet, best_f1 = assess(rows)

summary = {
    "timestamp_utc": ts,
    "runs_count": len(rows),
    "target": target,
    "best_scierc_f1_micro": best_f1,
    "meets_f1_target": meet["f1"],
    "meets_compliance_invariant": meet["comp"]
}

outdir = ROOT / "docs" / "scoreboards" / "phase7i"
outdir.mkdir(parents=True, exist_ok=True)
stamp = dt.datetime.utcnow().strftime("%Y%m%d-%H%M%S")
md = outdir / f"summary_{stamp}.md"
md.write_text("# Phase 7I — Baseline Summary\n\n"
              f"_Generated: {ts} UTC_\n\n"
              "## Runs\n\n" + md_table(rows) + "\n\n"
              "## Assessment\n\n"
              + json.dumps(summary, indent=2) + "\n",
              encoding="utf-8")

print(str(md))
