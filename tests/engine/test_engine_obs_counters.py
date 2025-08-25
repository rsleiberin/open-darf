from apps import obs
import importlib


def test_engine_obs_helper_counts_and_never_throws(monkeypatch):
    adapter = importlib.import_module("apps.api.adapter")
    obs.reset()
    # Normal path
    adapter._obs_emit_decision("ALLOW")
    adapter._obs_emit_decision("DENY")
    adapter._obs_emit_decision("INDETERMINATE")
    snap = obs.snapshot()
    assert snap["counters"].get("engine.decision.allow", 0) == 1
    assert snap["counters"].get("engine.decision.deny", 0) == 1
    assert snap["counters"].get("engine.decision.indeterminate", 0) == 1
    assert snap["counters"].get("engine.decision.total", 0) == 3
    # Failure path must not raise
    monkeypatch.setenv("OBS_FAIL_ON_EMIT", "1")
    adapter._obs_emit_decision("ALLOW")  # should not throw
    snap2 = obs.snapshot()
    assert snap2["last_error"] is not None
