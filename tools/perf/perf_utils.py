from __future__ import annotations
import time
import math
from typing import List, Dict


def percentiles(samples: List[float], ps=(50, 95, 99)) -> Dict[str, float]:
    if not samples:
        return {f"p{p}": 0.0 for p in ps}
    xs = sorted(samples)
    out = {}
    for p in ps:
        if len(xs) == 1:
            out[f"p{p}"] = xs[0]
            continue
        k = (p / 100) * (len(xs) - 1)
        f = math.floor(k)
        c = math.ceil(k)
        if f == c:
            out[f"p{p}"] = xs[int(k)]
        else:
            d0 = xs[f] * (c - k)
            d1 = xs[c] * (k - f)
            out[f"p{p}"] = d0 + d1
    return out


class Stopwatch:
    def __enter__(self):
        self.t0 = time.perf_counter()
        return self

    def __exit__(self, *a):
        self.dt_ms = (time.perf_counter() - self.t0) * 1000.0
