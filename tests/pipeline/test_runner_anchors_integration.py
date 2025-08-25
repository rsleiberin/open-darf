from apps.pipeline import run as pipeline_run


class _MemSource:
    def __init__(self, mapping):
        self._m = mapping

    def list(self):
        return list(self._m.keys())

    def fetch(self, ref):
        return self._m[ref]


def test_runner_anchors_flag_off(monkeypatch):
    monkeypatch.delenv("PIPELINE_ANCHORS", raising=False)
    src = _MemSource({"d1": b"hello world. another sentence."})
    count, path = pipeline_run.run_once(src, bucket="pipeline_e2e")
    assert count == 1


def test_runner_anchors_flag_on(monkeypatch):
    monkeypatch.setenv("PIPELINE_ANCHORS", "1")
    monkeypatch.setenv("PIPELINE_ANCHORS_SUB", "1")
    src = _MemSource({"d2": b"One. Two! Three?"})
    count, path = pipeline_run.run_once(src, bucket="pipeline_e2e")
    assert count == 1
