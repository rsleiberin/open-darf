#!/usr/bin/env python3
import json, sys, time, subprocess, os
from pathlib import Path

def repo_root() -> Path:
    try:
        out = subprocess.check_output(["git","rev-parse","--show-toplevel"], stderr=subprocess.DEVNULL)
        p = Path(out.decode().strip())
        if p.exists():
            return p
    except Exception:
        pass
    try:
        here = Path(__file__).resolve()
        for up in (3,2,1):
            if len(here.parents) > up:
                cand = here.parents[up]
                if (cand / ".git").exists():
                    return cand
        return here.parents[2]
    except Exception:
        pass
    return Path.cwd()

ROOT = repo_root()
receipts_dir = ROOT / "var/receipts/phase7i"
receipts = sorted(receipts_dir.glob("*/*/metrics.json"))

rows = []
for mpath in receipts:
    try:
        data = json.loads(Path(mpath).read_text())
    except Exception:
        continue
    core_ok = all(k in data and str(data[k]).strip() for k in ("dataset","model","split"))
    if not core_ok:
        continue
    def num(k, default=0.0):
        try: return float(data.get(k, default))
        except Exception: return default
    def to_int(v):
        try: return int(v if v is not None else 0)
        except Exception: return 0
    rows.append({
        "dataset": data["dataset"],
        "split": data["split"],
        "model": data["model"],
        "precision_micro": num("precision_micro",0.0),
        "recall_micro": num("recall_micro",0.0),
        "f1_micro": num("f1_micro",0.0),
        "f1_unlabeled": num("f1_unlabeled",0.0),
        "pred_count": to_int(data.get("pred_count",0)),
        "gold_pairs": to_int(data.get("gold_pairs",0)),
        "latency_ms": num("latency_ms",0.0),
        "constitutional_compliance_rate": num("constitutional_compliance_rate",0.0),
    })

out_dir = ROOT / "docs" / "scoreboards" / "phase7i"
out_dir.mkdir(parents=True, exist_ok=True)
stamp = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
summary_path = out_dir / f"summary_{stamp}.md"

with open(summary_path, "w") as f:
    f.write("# Phase 7I — Baseline Summary\n\n")
    f.write(f"_Generated: {time.strftime('%Y-%m-%d %H:%M:%SZ', time.gmtime())} UTC_\n\n")
    f.write("## Runs\n\n")
    if not rows:
        f.write("_No valid rows found._\n")
    else:
        headers = ["dataset","split","model","precision_micro","recall_micro","f1_micro","f1_unlabeled","pred_count","gold_pairs","latency_ms","constitutional_compliance_rate"]
        f.write("|" + "|".join(headers) + "|\n")
        f.write("|" + "|".join(["---"]*len(headers)) + "|\n")
        for r in rows:
            f.write("|" + "|".join(str(r[h]) for h in headers) + "|\n")

print(str(summary_path))
