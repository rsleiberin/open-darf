#!/usr/bin/env python3
import json, time, statistics, os, sys
def microbench(n_outer=10, n_inner=10000):
    # measure smallest measurable delta around a no-op
    mins=[]
    for _ in range(n_outer):
        best=1e9
        for _ in range(n_inner):
            t0=time.perf_counter()
            # no-op
            t1=time.perf_counter()
            d=t1-t0
            if d<best: best=d
        mins.append(best)
    return {
        "min_delta_s": min(mins),
        "median_min_delta_s": statistics.median(mins),
        "samples": len(mins),
        "inner_iters": n_inner
    }
def main():
    info=time.get_clock_info("perf_counter")
    mb=microbench()
    # acceptance: sub-ms means < 0.001s measurable
    result={
        "clock": {
            "implementation": getattr(time, "perf_counter").__name__,
            "resolution_s": info.resolution,
            "monotonic": info.monotonic,
            "adjustable": info.adjustable
        },
        "microbench": mb,
        "sub_ms_supported": mb["min_delta_s"] < 1e-3
    }
    json.dump(result, sys.stdout)
if __name__=="__main__":
    main()
