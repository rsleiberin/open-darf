from apps import obs


def test_obs_increment_and_histogram_never_throw(monkeypatch):
    obs.reset()
    # Normal path
    obs.increment("x", 1)
    obs.histogram("h", 5.0)
    snap = obs.snapshot()
    assert snap["counters"]["x"] == 1
    assert snap["histograms"]["h"]["n"] == 1
    # Failure path simulated by env
    monkeypatch.setenv("OBS_FAIL_ON_EMIT", "1")
    obs.increment("x", 1)  # should not throw
    obs.histogram("h", 6.0)  # should not throw
    snap2 = obs.snapshot()
    assert snap2["last_error"] is not None
