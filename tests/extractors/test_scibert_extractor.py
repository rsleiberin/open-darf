import os
import importlib
import pytest

MODULE = "apps.extractors.scibert_extractor"


def reload_mod():
    if MODULE in list(dict(importlib.sys.modules).keys()):
        importlib.sys.modules.pop(MODULE)
    return importlib.import_module(MODULE)


def test_stub_when_flag_off(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_SCI", "0")
    se = reload_mod()
    out = se.extract("Science examines heart rate of 70 bpm.")
    assert out["decision"] == "INDETERMINATE"
    assert out["guard_trace"][0]["status"] in ("skipped", "unavailable")


@pytest.mark.skipif(os.getenv("RUN_SCI_SMOKE") != "1", reason="SciBERT smoke disabled")
def test_smoke_when_flag_on_and_deps(monkeypatch):
    monkeypatch.setenv("EXTRACTOR_SCI", "1")
    se = reload_mod()
    out = se.extract("Insulin regulates blood glucose in diabetes mellitus.")
    assert "guard_trace" in out and out["decision"] == "INDETERMINATE"
    # entities may be empty depending on local model availability; just assert dict shape
    assert isinstance(out.get("entities"), list)
