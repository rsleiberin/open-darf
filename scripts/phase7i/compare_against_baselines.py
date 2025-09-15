#!/usr/bin/env python3
import json, glob, pathlib, datetime as dt

ROOT = pathlib.Path(__file__).resolve().parents[2]
runs = []
for mf in glob.glob(str(ROOT / "var" / "receipts" / "phase7i" / "*" / "*" / "metrics.json")):
    try:
        runs.append(json.loads(pathlib.Path(mf).read_text(encoding="utf-8")))
    except Exception:
        pass

lit_path = ROOT / "docs" / "scoreboards" / "phase7i" / "literature_baselines.json"
try:
    literature = json.loads(lit_path.read_text(encoding="utf-8"))
except Exception:
    literature = []

def row(ds, split, model, metrics):
    return {
        "dataset": ds, "split": split, "model": model,
        "precision_micro": metrics.get("precision_micro"),
        "recall_micro": metrics.get("recall_micro"),
        "f1_micro": metrics.get("f1_micro")
    }

def best_of(model_name, dataset, split):
    # pick best f1 for our runs matching model and dataset split
    best=None; best_f1=-1.0
    for r in runs:
        if r.get("model") in (model_name.lower(), model_name.upper(), model_name, model_name.replace("-","")) and \
           r.get("dataset")==dataset and r.get("split")==split:
            f1 = float(r.get("f1_micro",0.0) or 0.0)
            if f1 > best_f1:
                best_f1 = f1; best = r
    return best

def md_table(rows):
    hdr = ["dataset","split","model","precision_micro","recall_micro","f1_micro"]
    out = ["|"+"|".join(hdr)+"|", "|"+"|".join(["---"]*len(hdr))+"|"]
    for r in rows:
        out.append("|"+"|".join(str(r.get(k,"")) for k in hdr)+"|")
    return "\n".join(out)

compare_rows=[]
# Literature rows
for lb in literature:
    compare_rows.append(row(lb["dataset"], lb["split"], lb["model"], lb))

# Our best rows per baseline slot
for lb in literature:
    ours = best_of(lb["model"], lb["dataset"], lb["split"])
    if ours:
        tag = f"DARF/{ours.get('model')}"
        compare_rows.append(row(ours["dataset"], ours["split"], tag, ours))

stamp = dt.datetime.utcnow().strftime("%Y%m%d-%H%M%S")
md_path = ROOT / "docs" / "scoreboards" / "phase7i" / f"comparison_{stamp}.md"
md_path.write_text(
    "# Phase 7I — Competitive Comparison\n\n"
    "_Populate literature_baselines.json with actual numbers, then re-run._\n\n"
    + md_table(compare_rows) + "\n",
    encoding="utf-8"
)
print(str(md_path))
