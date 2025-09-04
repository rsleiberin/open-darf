from __future__ import annotations
import argparse, json, statistics, sys
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

def load_jsonl(p: Path) -> Iterable[dict]:
    with p.open("r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)

def pct(values: List[float], q: float) -> float:
    if not values:
        return 0.0
    values_sorted = sorted(values)
    idx = int(round((len(values_sorted)-1) * q))
    return float(values_sorted[idx])

def summarize(audit_paths: List[Path]) -> dict:
    # Aggregate by decision and stage
    by_decision: Dict[str, int] = {}
    by_stage: Dict[str, int] = {}
    durations: Dict[Tuple[str,str], List[float]] = {}  # (stage, decision) -> [ms]

    total = 0
    for ap in audit_paths:
        for ev in load_jsonl(ap):
            total += 1
            d = str(ev.get("decision","")).upper()
            s = str(ev.get("stage",""))
            by_decision[d] = by_decision.get(d, 0) + 1
            by_stage[s] = by_stage.get(s, 0) + 1
            ms = ev.get("duration_ms")
            if isinstance(ms, (int, float)):
                durations.setdefault((s,d), []).append(float(ms))

    # Timing stats
    timing = {}
    for (stage, decision), vals in durations.items():
        timing.setdefault(stage, {})
        timing[stage][decision] = {
            "count": len(vals),
            "mean_ms": (sum(vals)/len(vals)) if vals else 0.0,
            "p50_ms": pct(vals, 0.50),
            "p95_ms": pct(vals, 0.95),
            "p99_ms": pct(vals, 0.99),
        }

    return {
        "events_total": total,
        "by_decision": by_decision,
        "by_stage": by_stage,
        "timing": timing,
    }

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Blocking effectiveness & timing report")
    ap.add_argument("--audits", nargs="+", required=True, help="Paths to audit JSONL files")
    ap.add_argument("--out", required=True, help="Output JSON file")
    args = ap.parse_args(argv)

    paths = [Path(p) for p in args.audits]
    for p in paths:
        if not p.exists():
            print(f"error: audit file not found: {p}", file=sys.stderr)
            return 2

    rep = summarize(paths)
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump(rep, fh, ensure_ascii=False, indent=2)
    print(json.dumps({"ok": True, "out": args.out}, ensure_ascii=False))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
