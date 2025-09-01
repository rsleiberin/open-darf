#!/usr/bin/env python3
import argparse
import json
import glob
import os
import time


def latest_run(root, task):
    ps = glob.glob(os.path.join(root, task, "*"))
    return sorted(ps)[-1] if ps else None


def load_summary(run_dir):
    try:
        return json.load(open(os.path.join(run_dir, "summary.json")))
    except Exception:
        return {}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", choices=["scierc", "biored"], required=True)
    ap.add_argument("--receipts", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--target_f1", type=float, default=None)
    ap.add_argument("--ner_target", type=float, default=None)
    ap.add_argument("--re_target", type=float, default=None)
    args = ap.parse_args()

    run = latest_run(args.receipts, args.task)
    if not run:
        json.dump({"error": "no_runs"}, open(args.out, "w"))
        print("no runs")
        return 2
    s = load_summary(run)
    ent = s.get("micro", {}).get("entity_f1", 0.0)
    rel = s.get("micro", {}).get("relation_f1", 0.0)
    result = {
        "task": args.task,
        "run_path": run,
        "entity_f1": ent,
        "relation_f1": rel,
        "targets": {},
        "pass": True,
    }
    if args.task == "scierc":
        tgt = float(args.target_f1 if args.target_f1 is not None else 0.67)
        result["targets"]["entity_f1"] = tgt
        result["pass"] = bool(ent >= tgt)
    else:
        ner_t = float(args.ner_target if args.ner_target is not None else 0.90)
        re_t = float(args.re_target if args.re_target is not None else 0.65)
        result["targets"]["entity_f1"] = ner_t
        result["targets"]["relation_f1"] = re_t
        result["pass"] = bool(ent >= ner_t and rel >= re_t)

    result["generated_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    with open(args.out, "w") as f:
        json.dump(result, f, indent=2)
    print(
        json.dumps(
            {
                "wrote": args.out,
                "pass": result["pass"],
                "entity_f1": ent,
                "relation_f1": rel,
            }
        )
    )


if __name__ == "__main__":
    main()
