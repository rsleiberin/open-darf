#!/usr/bin/env python3
import argparse
import json
import os
import glob
import subprocess
import time
import platform

ap = argparse.ArgumentParser()
ap.add_argument("--receipts", required=True)
ap.add_argument("--out", required=True)
args = ap.parse_args()


def latest(p):
    xs = glob.glob(os.path.join(p, "*"))
    return sorted(xs)[-1] if xs else None


def run(cmd):
    try:
        return subprocess.check_output(cmd, text=True).strip()
    except Exception:
        return None


root = args.receipts
sc = latest(os.path.join(root, "scierc"))
bi = latest(os.path.join(root, "biored"))


def load(p):
    try:
        return json.load(open(p))
    except Exception:
        return None


prov = {
    "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    "git": {
        "commit": run(["git", "rev-parse", "HEAD"]),
        "branch": run(["git", "rev-parse", "--abbrev-ref", "HEAD"]),
        "remote_origin": run(["git", "config", "--get", "remote.origin.url"]),
    },
    "env": {
        "python": platform.python_version(),
        "torch": (
            run(
                [
                    "python",
                    "- <<'PY'\nimport torch, json; print(getattr(torch,'__version__',None))\nPY",
                ]
            )
            or ""
        ).strip(),
    },
    "runs": {
        "scierc": {
            "path": sc,
            "summary": load(os.path.join(sc, "summary.json")) if sc else None,
        },
        "biored": {
            "path": bi,
            "summary": load(os.path.join(bi, "summary.json")) if bi else None,
        },
    },
    "gates": load("var/reports/phase6c/gates.json"),
}
os.makedirs(os.path.dirname(args.out), exist_ok=True)
json.dump(prov, open(args.out, "w"), indent=2)
print(json.dumps({"wrote": args.out}))
