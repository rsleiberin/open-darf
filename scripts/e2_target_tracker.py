#!/usr/bin/env python3
import json, glob, pathlib, argparse, time

def newest(paths):
    return sorted(paths, key=lambda p: pathlib.Path(p).stat().st_mtime if pathlib.Path(p).exists() else 0)[-1] if paths else None

def load_best_metrics():
    # Prefer PURE runs (even bridged), fallback to heuristic relation_baseline
    pure = glob.glob("var/receipts/phase7g/pure_runs/*/metrics.json")
    relx = glob.glob("var/receipts/phase7g/relation_baseline/run/*/metrics.json")
    candidates = []
    for fp in pure + relx:
        p = pathlib.Path(fp)
        try:
            obj = json.loads(p.read_text())
        except Exception:
            continue
        if obj.get("dataset") != "SciERC" or obj.get("split") != "dev":
            continue
        f1 = obj.get("f1_micro")
        if f1 is None: 
            continue
        obj["__file"] = str(p)
        obj["__mtime"] = p.stat().st_mtime
        candidates.append(obj)
    if not candidates:
        return None
    # best by F1_micro, tiebreaker by newest
    candidates.sort(key=lambda o: (o.get("f1_micro", -1), o.get("__mtime", 0)))
    return candidates[-1]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", type=float, default=0.50, help="Target F1 (micro) for E2")
    ap.add_argument("--out", type=str, default=None, help="Where to write readiness JSON")
    args = ap.parse_args()

    best = load_best_metrics()
    now = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    if best is None:
        report = {"status":"no_data","timestamp":now,"reason":"no SciERC-dev metrics found"}
        print(json.dumps(report, indent=2))
        if args.out: pathlib.Path(args.out).write_text(json.dumps(report, indent=2))
        return 0

    f1 = float(best.get("f1_micro", 0.0))
    delta = round(args.target - f1, 6)
    status = "pass" if f1 >= args.target else "gap"
    report = {
        "status": status,
        "timestamp": now,
        "target_f1_micro": args.target,
        "best_f1_micro": f1,
        "delta_to_target": max(0.0, delta),
        "model": best.get("model"),
        "source_receipt": best.get("__file"),
        "precision_micro": best.get("precision_micro"),
        "recall_micro": best.get("recall_micro"),
        "f1_unlabeled": best.get("f1_unlabeled"),
        "notes": best.get("notes", "")
    }
    print(json.dumps(report, indent=2))
    if args.out:
        pathlib.Path(args.out).write_text(json.dumps(report, indent=2))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
