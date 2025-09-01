#!/usr/bin/env python3
import argparse
import json
import sys
from pathlib import Path


def ensure_pkg(modname, pip_name=None):
    try:
        __import__(modname)
        return True
    except Exception:
        import subprocess

        pn = pip_name or modname
        subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", pn])
        __import__(modname)
        return True


def try_load(name_candidates):
    from datasets import load_dataset

    last_err = None
    for name in name_candidates:
        try:
            ds = load_dataset(name)
            return name, ds
        except Exception as e:
            last_err = e
    raise RuntimeError(
        f"Failed to load dataset via candidates {name_candidates}: {last_err}"
    )


def export_splits(ds, out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    # Prefer standard split names; save as JSONL
    for split in ["train", "validation", "dev", "test"]:
        if split in ds:
            path = out_dir / f"{split}.jsonl"
            ds[split].to_json(str(path))  # hf datasets supports to_json
    # minimal manifest
    (out_dir / "MANIFEST.json").write_text(
        json.dumps(
            {
                "splits": [
                    s for s in ["train", "validation", "dev", "test"] if s in ds
                ],
                "num_rows": {
                    s: len(ds[s])
                    for s in ds
                    if s in ["train", "validation", "dev", "test"]
                },
            },
            indent=2,
        )
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("benchmark", choices=["scierc", "biored"])
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    ensure_pkg("datasets")

    candidates = {
        "scierc": ["scierc", "allenai/scierc", "ai2_scierc"],
        "biored": ["biored", "ncbi/biored", "allenai/biored"],
    }[args.benchmark]

    out_dir = Path(args.out)
    try:
        name_used, ds = try_load(candidates)
    except Exception as e:
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "ERROR.txt").write_text(str(e))
        print(f"[ERROR] Could not load {args.benchmark}: {e}", file=sys.stderr)
        sys.exit(2)

    export_splits(ds, out_dir)
    print(
        json.dumps(
            {"benchmark": args.benchmark, "source": name_used, "out": str(out_dir)},
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
