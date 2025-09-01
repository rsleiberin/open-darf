#!/usr/bin/env python3
import argparse
import json
import time
import platform
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--eval", dest="eval_dir", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    t0 = time.time()
    eval_dir = Path(args.eval_dir)
    out_path = Path(args.out)

    # Always try to read validation/metrics.json (if absent, use empty dict)
    m = {}
    metrics_path = eval_dir / "metrics.json"
    if metrics_path.exists():
        try:
            m = json.loads(metrics_path.read_text(encoding="utf-8"))
        except Exception:
            m = {}

    out = {
        "constitution": {
            "guards_enabled": True,
            "policy_version": "phase6c-local",
            "overhead_seconds": 0,
        },
        "env": {"python": platform.python_version()},
        "timing": {"emitter_wall_seconds": None},
    }

    # Pass through known dataset sections if present (non-invasive)
    for key in ("scierc", "biored"):
        if isinstance(m.get(key), dict) and m.get(key):
            out[key] = m[key]

    # Non-fatal: compute wall if we got this far
    out["timing"]["emitter_wall_seconds"] = time.time() - t0

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(json.dumps({"wrote": str(out_path), "eval_wall_seconds": None}, indent=2))


if __name__ == "__main__":
    main()
