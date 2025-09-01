#!/usr/bin/env python3
"""
CI verifier for gates.json.

- Ensures dataset sections exist
- Enforces non-regression vs baselines (with small tolerance)
- Emits a concise JSON summary and proper exit code
"""
import json
import sys
from pathlib import Path

GATES = Path("var/reports/phase6c/gates.json")

# Baselines (numbers to beat)
BASELINES = {
    "scierc": {"entity_f1": 0.30703012912482064},  # P=0.3579 R=0.2688 F1=0.3070
    "biored": {"entity_f1": 0.6310494357786541},  # P=0.8157 R=0.5146 F1=0.6310
}
TOL = 1e-6  # float tolerance


def fail(msg, payload=None, code=2):
    out = {"ok": False, "reason": msg}
    if payload:
        out["details"] = payload
    print(json.dumps(out, indent=2))
    sys.exit(code)


def main():
    if not GATES.exists():
        fail("gates.json not found", {"path": str(GATES)})

    try:
        g = json.loads(GATES.read_text(encoding="utf-8"))
    except Exception as e:
        fail("gates.json unreadable", {"error": str(e)})

    missing = [k for k in ("scierc", "biored") if k not in g]
    if missing:
        fail("dataset sections missing", {"missing": missing})

    results = {"ok": True, "checks": []}
    for ds, reqs in BASELINES.items():
        if ds not in g or not isinstance(g[ds], dict):
            fail(f"{ds} section absent or not an object")
        for metric, baseline in reqs.items():
            val = g[ds].get(metric, None)
            if val is None:
                fail(f"{ds}.{metric} missing")
            # Non-regression: val >= baseline - tol
            if val + TOL < baseline:
                fail(
                    "non-regression check failed",
                    {
                        "dataset": ds,
                        "metric": metric,
                        "value": val,
                        "baseline_min": baseline,
                    },
                )
            results["checks"].append(
                {
                    "dataset": ds,
                    "metric": metric,
                    "value": val,
                    "baseline_min": baseline,
                }
            )

    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
