import json
from pathlib import Path

import importlib

from apps.pipeline import run as pipeline_run  # imports run_once


class _MemSource:
    def __init__(self, mapping):
        self._m = mapping

    def list(self):
        return list(self._m.keys())

    def fetch(self, ref):
        return self._m[ref]


def _load_receipt(path: str):
    p = Path(path)
    assert p.exists(), f"receipt path not found: {p}"
    return json.loads(p.read_text(encoding="utf-8"))


def test_runner_cbdt_flag_off(monkeypatch, tmp_path):
    # Ensure flag is OFF
    monkeypatch.delenv("PIPELINE_CBDT", raising=False)
    monkeypatch.setenv("PIPELINE_PERF", "1")

    src = _MemSource({"doc-1": b"Clearly undeniable text."})
    count, path = pipeline_run.run_once(src, bucket="pipeline_e2e")
    assert count == 1

    payload = _load_receipt(path)
    rpt = payload["reports"]["doc-1"]
    assert "cbdt" not in rpt  # gated off
    assert "parser" in rpt and "bias" in rpt


def test_runner_cbdt_flag_on_emits(monkeypatch, tmp_path):
    monkeypatch.setenv("PIPELINE_CBDT", "1")
    monkeypatch.setenv("PIPELINE_CBDT_PROVIDER", "local")
    monkeypatch.setenv("PIPELINE_PERF", "1")

    src = _MemSource({"doc-2": b"Experts say this is clearly true."})
    count, path = pipeline_run.run_once(src, bucket="pipeline_e2e")
    assert count == 1

    payload = _load_receipt(path)
    cbdt = payload["reports"]["doc-2"].get("cbdt")
    assert cbdt, "expected cbdt section when flag ON"
    assert cbdt.get("findings_total", 0) >= 1
    # If present, perf stats should include parse/process; cbdt perf bucket optional
    perf = payload.get("perf", {})
    assert "parse_ms" in perf and "process_ms" in perf


def test_runner_cbdt_never_throws(monkeypatch, tmp_path):
    # Force cbdt_pass to raise; runner must swallow and report error
    monkeypatch.setenv("PIPELINE_CBDT", "1")
    monkeypatch.setenv("PIPELINE_PERF", "1")

    # Import module once so we can monkeypatch the symbol it will import lazily
    mod = importlib.import_module("apps.pipeline.process.cbdt")

    def boom(*a, **k):  # raises at call time
        raise RuntimeError("kaboom")

    monkeypatch.setattr(mod, "cbdt_pass", boom, raising=True)

    src = _MemSource({"doc-3": b"Some say it might be true."})
    count, path = pipeline_run.run_once(src, bucket="pipeline_e2e")
    assert count == 1

    payload = _load_receipt(path)
    cbdt = payload["reports"]["doc-3"].get("cbdt")
    assert cbdt and cbdt.get("error") in {"RuntimeError", "Exception"}
