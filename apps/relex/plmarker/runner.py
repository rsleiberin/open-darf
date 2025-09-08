#!/usr/bin/env python3
import sys, json, argparse, time, pathlib

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset_dir", required=True)
    ap.add_argument("--split", default="dev")
    ap.add_argument("--outdir", required=True)
    args = ap.parse_args()

    outdir = pathlib.Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    # Detect heavy deps
    try:
        import torch  # noqa: F401
        import transformers  # noqa: F401
        status = "ready"
    except Exception:
        status = "deps_missing"

    receipt = {
        "status": status,
        "dataset_dir": args.dataset_dir,
        "split": args.split,
        "outdir": str(outdir),
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    }
    (outdir/"runner_stdout.json").write_text(json.dumps(receipt)+"\n")

    if status != "ready":
        print(json.dumps(receipt))
        return 0

    # Placeholder: where real PL-Marker inference/eval will go.
    print(json.dumps({"status":"not_implemented","note":"PL-Marker inference pending"}))
    return 0

if __name__ == "__main__":
    sys.exit(main())
