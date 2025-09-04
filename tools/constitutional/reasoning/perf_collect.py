from __future__ import annotations
import json, os, time
from time import perf_counter_ns
from typing import Dict
from .engine import ExplanationEngine
from .context import ReasoningInput
from .quality import quality_score
from .perf_monitor import PerfStats

def run_collect(iterations: int = 5000) -> Dict:
    eng = ExplanationEngine()
    rin = ReasoningInput(decision="ACCEPTABLE", principles=["sovereignty","safety"], rationale="allow provenance-verified", evidence_ids=["doc:demo"])
    stats = PerfStats()
    # warmup
    for _ in range(500):
        eng.explain(rin)
    for _ in range(iterations):
        t0 = perf_counter_ns()
        exp = eng.explain(rin)
        stats.record(perf_counter_ns() - t0)
    pct = stats.percentiles()
    exp = eng.explain(rin)
    q = quality_score(exp)
    return {
        "iterations": iterations,
        "percentiles_ns": pct,
        "quality": q,
        "ts": time.time(),
    }

def main():
    out = run_collect(int(os.getenv("ITER", "5000")))
    outpath = os.getenv("REASONING_PERF_OUT", "").strip()
    data = json.dumps(out, ensure_ascii=False, indent=2)
    if outpath:
        os.makedirs(os.path.dirname(outpath), exist_ok=True)
        with open(outpath, "w", encoding="utf-8") as f:
            f.write(data)
        print(outpath)
    else:
        print(data)

if __name__ == "__main__":
    main()
