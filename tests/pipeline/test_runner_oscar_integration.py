from apps.pipeline import run as pipeline_run


class _MemSource:
    def __init__(self, mapping):
        self._m = mapping

    def list(self):
        return list(self._m.keys())

    def fetch(self, ref):
        return self._m[ref]


def test_runner_oscar_flag_off(monkeypatch):
    monkeypatch.delenv("PIPELINE_OSCAR", raising=False)
    src = _MemSource({"x1": b"hello world"})
    cnt, path = pipeline_run.run_once(src, bucket="pipeline_e2e")
    assert cnt == 1


def test_runner_oscar_flag_on(monkeypatch):
    monkeypatch.setenv("PIPELINE_OSCAR", "1")
    monkeypatch.setenv("PIPELINE_PERF", "1")
    src = _MemSource({"x2": b"Clearly undeniable. Experts say it might be true."})
    cnt, path = pipeline_run.run_once(src, bucket="pipeline_e2e")
    assert cnt == 1
