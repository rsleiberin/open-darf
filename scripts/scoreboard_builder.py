#!/usr/bin/env python3
import os, json, glob, datetime as dt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT  = ROOT / "docs" / "scoreboards" / "phase8" / "SUMMARY.md"

def load_json(p):
    try:
        with open(p, encoding="utf-8") as f: return json.load(f)
    except Exception:
        return None

def find_receipts():
    # Phase 7H full-suite + any Phase 8 receipts that get added later
    patterns = [
        "var/receipts/phase7h/full_suite/*/*/re_eval_metrics.json",
        "var/receipts/phase8/**/re_eval_metrics.json",
    ]
    files = []
    for pat in patterns:
        files.extend(glob.glob(str(ROOT / pat), recursive=True))
    return sorted(files)

def row_from_metrics(path):
    m = load_json(path)
    if not m: return None
    # attempt to find dataset folder name one level up from suite
    suite_dir = Path(path).parent
    dataset   = suite_dir.parent.name
    return {
        "dataset": dataset,
        "model": m.get("model","<unknown>"),
        "split": m.get("split","<na>"),
        "precision": m.get("precision_micro"),
        "recall": m.get("recall_micro"),
        "f1": m.get("f1_micro"),
        "f1_unlabeled": m.get("f1_unlabeled"),
        "compliance": m.get("constitutional_compliance_rate"),
        "pred_count": m.get("pred_count"),
        "gold_pairs": m.get("gold_pairs"),
        "latency_ms": m.get("latency_ms"),
        "receipt": os.path.relpath(path, ROOT),
    }

def main():
    files = find_receipts()
    rows = [r for p in files if (r:=row_from_metrics(p))]

    ts = dt.datetime.utcnow().strftime("%Y-%m-%d %H:%M:%SZ")
    lines = []
    lines.append(f"# Phase 8 Scoreboard — {ts}")
    lines.append("")
    lines.append("Receipts-driven leaderboard compiled from `re_eval_metrics.json` found under:")
    lines.append("- `var/receipts/phase7h/full_suite/*/*` (identity/plumbing)")
    lines.append("- `var/receipts/phase8/**` (real baselines: PURE / PL-Marker / heuristic)")
    lines.append("")
    if not rows:
        lines.append("> No receipts found yet. Run Phase 8 baselines to populate this table.")
    else:
        # Sort: dataset, then by (model, split)
        rows.sort(key=lambda r: (r["dataset"], r["model"], r["split"]))
        # Header
        lines.append("| dataset | model | split | precision | recall | f1 | comp | preds | gold | latency_ms | receipt |")
        lines.append("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---|")
        for r in rows:
            lines.append(
                f"| {r['dataset']} | {r['model']} | {r['split']} | "
                f"{r['precision']} | {r['recall']} | {r['f1']} | {r['compliance']} | "
                f"{r['pred_count']} | {r['gold_pairs']} | {r['latency_ms']} | {r['receipt']} |"
            )
    # Targets section (explicit)
    lines.append("\n## Targets (must meet before any open-source packaging)")
    lines.append("- **SciERC**: F1_micro ≥ 0.50 (PURE / PL-Marker)")
    lines.append("- **BioRED**: entity ≥ 0.90, relation ≥ 0.65")
    lines.append("\n## Notes")
    lines.append("- Phase 7H identity-eval rows will show F1=1.0; these validate plumbing, not model accuracy.")
    lines.append("- Phase 8 model rows (PURE / PL-Marker / heuristic) will determine acceptance vs targets.")
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(lines), encoding="utf-8")
    print(f"[OK] Wrote {OUT}")

if __name__ == "__main__":
    main()
