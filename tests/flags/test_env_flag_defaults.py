import os
import pytest

FLAGS = [
    "EXTRACTOR_SCI",
    "EXTRACTOR_BIO",
    "EXTRACTOR_TEXT2NKG",
    "TEMPORAL_GRAPH_MODEL",
    "RUN_PERF",
]


@pytest.fixture(autouse=True)
def _reset_flags(monkeypatch):
    for k in FLAGS:
        monkeypatch.setenv(k, "0")


def test_flags_default_zero():
    for k in FLAGS:
        assert os.getenv(k) in ("0", None)
