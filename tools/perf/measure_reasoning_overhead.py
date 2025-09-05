#!/usr/bin/env python3
"""
Phase 7E perf receipt generator for ExplanationEngine.explain().
- Imports via package path so relative imports resolve on CLI runs.
- Constructs a valid ReasoningInput (decision, principles, rationale).
- Records micro-overhead percentiles with PerfStats.
- Writes a timestamped JSON receipt under var/receipts/phase7e/perf/.
"""
from __future__ import annotations
import argparse, json, os, time
from pathlib import Path
from statistics import mean
from time import perf_counter_ns
import sys

# Ensure repo root on sys.path
HERE = Path(__file__).resolve()
REPO = HERE.parents[3]  # .../tools/perf -> .../tools -> REPO
sys.path.insert(0, str(REPO))

# Imports via package path
from tools.constitutional.reasoning.engine import ExplanationEngine
from tools.constitutional.reasoning.context import ReasoningInput
from tools.constitutional.reasoning.perf_monitor import PerfStats

def run_once(n: int, decision: str, principles: list[str], rationale: str, precedents: tuple[str, ...]) -> dict:
    eng = ExplanationEngine()
    rin = ReasoningInput(decision=decision, principles=principles, rationale=rationale)
    # Warmup
    for _ in range(min(100, max(10, n//100))):
        eng.explain(rin, precedents=precedents)
    ps = PerfStats()
    durations = []
    for _ in range(n):
        t0 = perf_counter_ns()
        eng.explain(rin, precedents=precedents)
        t1 = perf_counter_ns()
        dt = t1 - t0
        ps.record(dt)
        durations.append(dt)
    pct = ps.percentiles()
    out = {
        "operation": "ExplanationEngine.explain",
        "n": n,
        "p50_ns": pct.get("p50"),
        "p95_ns": pct.get("p95"),
        "max_ns": max(durations),
        "min_ns": min(durations),
        "mean_ns": int(mean(durations)),
        "env": {"python": sys.version.split()[0]},
        "input": {"decision": decision, "principles": principles, "rationale": rationale, "precedents": list(precedents)},
        "repo_rel": str(HERE.relative_to(REPO)),
        "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--iters", type=int, default=5000)
    ap.add_argument("--decision", default="ACCEPTABLE")
    ap.add_argument("--principle", action="append", dest="principles", default=["sovereignty","safety"])
    ap.add_argument("--rationale", default="deny leakage; allow provenance-verified content")
    ap.add_argument("--precedent", action="append", dest="precedents", default=["prec:alpha"])
    args = ap.parse_args()

    res = run_once(
        n=args.iters,
        decision=args.decision,
        principles=list(args.principles),
        rationale=args.rationale,
        precedents=tuple(args.precedents),
    )

    outdir = REPO / "var" / "receipts" / "phase7e" / "perf" / time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir.mkdir(parents=True, exist_ok=True)
    outpath = outdir / "reasoning_overhead.json"
    outpath.write_text(json.dumps(res, indent=2), encoding="utf-8")
    print(json.dumps({"wrote": str(outpath), "n": res["n"], "p50_ns": res["p50_ns"], "p95_ns": res["p95_ns"]}, indent=2))

if __name__ == "__main__":
    main()
