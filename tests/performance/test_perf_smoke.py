import time


def test_perf_smoke_under_100ms():
    t0 = time.time()
    # placeholder path for future realistic microbenchmarks
    sum(range(10000))
    assert (time.time() - t0) * 1000 < 100.0
