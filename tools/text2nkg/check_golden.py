from __future__ import annotations
import argparse, json, sys
from pathlib import Path
from typing import Tuple, Dict, Any

DEFAULT_DEV = 0.20485
DEFAULT_TEST = 0.20446

def _read_json(p: Path) -> Dict[str, Any]:
    return json.loads(p.read_text(encoding="utf-8"))

def _extract_strict_f1s(obj: Dict[str, Any]) -> Tuple[float, float]:
    """
    Try a few formats:
      A) {"strict":{"dev":{"f1":...},"test":{"f1":...}}}
      B) {"dev":{"strict":{"f1":...}},"test":{"strict":{"f1":...}}}
      C) {"strict":{"f1":...}}  # not split; return same for both
    """
    if "strict" in obj and isinstance(obj["strict"], dict):
        s = obj["strict"]
        if "dev" in s and "test" in s and isinstance(s["dev"], dict) and isinstance(s["test"], dict):
            return float(s["dev"].get("f1", 0.0)), float(s["test"].get("f1", 0.0))
        if "f1" in s and isinstance(s["f1"], (int, float)):
            return float(s["f1"]), float(s["f1"])
    if "dev" in obj and "test" in obj:
        try:
            return float(obj["dev"]["strict"]["f1"]), float(obj["test"]["strict"]["f1"])
        except Exception:
            pass
    # Fallback: missing
    return 0.0, 0.0

def main():
    ap = argparse.ArgumentParser(description="Check dev/test strict F1 against golden within tolerance.")
    ap.add_argument("--dev-scoreboard", required=True, help="Path to dev scoreboard.json")
    ap.add_argument("--test-scoreboard", required=True, help="Path to test scoreboard.json")
    ap.add_argument("--golden", required=False, help="Path to golden scoreboard JSON")
    ap.add_argument("--tol", type=float, default=0.002, help="Absolute tolerance for F1 difference (default: 0.002)")
    args = ap.parse_args()

    dev_json = _read_json(Path(args.dev_scoreboard))
    test_json = _read_json(Path(args.test_scoreboard))

    dev_f1 = float(dev_json.get("strict", {}).get("f1", 0.0))
    test_f1 = float(test_json.get("strict", {}).get("f1", 0.0))

    if args.golden:
        g = _read_json(Path(args.golden))
        gold_dev, gold_test = _extract_strict_f1s(g)
    else:
        gold_dev, gold_test = DEFAULT_DEV, DEFAULT_TEST

    d_ok = abs(dev_f1 - gold_dev) <= args.tol
    t_ok = abs(test_f1 - gold_test) <= args.tol

    report = {
        "golden": {"dev": gold_dev, "test": gold_test},
        "observed": {"dev": dev_f1, "test": test_f1},
        "tol": args.tol,
        "pass": bool(d_ok and t_ok),
        "dev_delta": dev_f1 - gold_dev,
        "test_delta": test_f1 - gold_test,
    }
    print(json.dumps(report, indent=2))
    sys.exit(0 if report["pass"] else 3)

if __name__ == "__main__":
    main()
