from apps import obs
from apps.pipeline import run as pipeline_run


class _MemSource:
    def __init__(self, mapping):
        self._m = mapping

    def list(self):
        return list(self._m.keys())

    def fetch(self, ref):
        return self._m[ref]


def test_runner_emits_counters(monkeypatch):
    obs.reset()
    monkeypatch.setenv("PIPELINE_PERF", "1")
    monkeypatch.setenv("PIPELINE_CBDT", "1")
    monkeypatch.setenv("PIPELINE_CBDT_PROVIDER", "local")
    src = _MemSource({"r1": b"clearly undeniable. experts say."})
    cnt, path = pipeline_run.run_once(src, bucket="pipeline_e2e")
    snap = obs.snapshot()
    assert snap["counters"].get("runner.cbdt.runs", 0) == 1
    assert snap["counters"].get("runner.cbdt.findings_total", 0) >= 1
    assert snap["histograms"].get("runner.cbdt.ms", {}).get("n", 0) == 1
