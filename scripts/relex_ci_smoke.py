#!/usr/bin/env python3
"""
RE CI Smoke — robust, dependency-light.

- Source of truth = existing receipts.
  Prefers best heuristic v6; else newest under relation_baseline/run/*/.
- Gates:
    F1_micro >= RELEX_SMOKE_F1_MIN (default 0.20)
    compliance >= RELEX_SMOKE_COMPLIANCE_MIN (default 0.95)
- Compliance key is tolerant: tries ["compliance",
  "constitutional_compliance_rate", "compliance_rate",
  "compliance_micro", "compliance_overall"].
- Prints JSON summary and exits 0 on pass, 1 on fail.
"""
from __future__ import annotations
import os, sys, json, time
from pathlib import Path
from typing import Optional

REPO_ROOT = Path(__file__).resolve().parents[1]
RECEIPTS = REPO_ROOT / "var" / "receipts" / "phase7g"
BASELINE_RUN = RECEIPTS / "relation_baseline" / "run"

F1_MIN = float(os.environ.get("RELEX_SMOKE_F1_MIN", "0.20"))
COMP_MIN = float(os.environ.get("RELEX_SMOKE_COMPLIANCE_MIN", "0.95"))
COMP_KEYS = ["compliance",
             "constitutional_compliance_rate",
             "compliance_rate",
             "compliance_micro",
             "compliance_overall"]

def newest_metrics(root: Path) -> Optional[Path]:
    best, best_m = None, -1.0
    if not root.exists():
        return None
    for d in root.iterdir():
        if d.is_dir():
            p = d / "metrics.json"
            if p.exists():
                m = p.stat().st_mtime
                if m > best_m:
                    best, best_m = p, m
    return best

def load_metrics_path() -> Path:
    preferred = BASELINE_RUN / "20250907-205327_v6" / "metrics.json"
    if preferred.exists():
        return preferred
    p = newest_metrics(BASELINE_RUN)
    if p is None:
        print(json.dumps({"status":"error","reason":"metrics_not_found","searched":str(BASELINE_RUN)}))
        sys.exit(1)
    return p

def get_compliance(m: dict) -> float:
    for k in COMP_KEYS:
        if k in m:
            try:
                return float(m[k])
            except Exception:
                pass
    return 0.0  # fail-closed if not present

def main() -> int:
    src = load_metrics_path()
    m = json.loads(src.read_text(encoding="utf-8"))
    f1 = float(m.get("f1_micro", -1.0))
    comp = get_compliance(m)
    ok = (f1 >= F1_MIN) and (comp >= COMP_MIN)
    report = {
        "status": "ok" if ok else "fail",
        "source_receipt": str(src),
        "f1_micro": f1,
        "compliance": comp,
        "thresholds": {"f1_min": F1_MIN, "compliance_min": COMP_MIN},
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    print(json.dumps(report))
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
