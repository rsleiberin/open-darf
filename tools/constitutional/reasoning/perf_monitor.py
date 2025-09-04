from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Dict
import statistics

@dataclass
class PerfStats:
    samples_ns: List[int] = field(default_factory=list)

    def record(self, ns: int) -> None:
        self.samples_ns.append(ns)

    def percentiles(self) -> Dict[str, float]:
        if not self.samples_ns:
            return {"p50": 0.0, "p95": 0.0, "p99": 0.0}
        xs = sorted(self.samples_ns)
        def pct(p):
            idx = max(0, min(len(xs)-1, int(round((p/100.0)*len(xs))-1)))
            return float(xs[idx])
        return {"p50": pct(50), "p95": pct(95), "p99": pct(99)}
