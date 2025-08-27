import pytest


@pytest.fixture(autouse=True)
def isolate_flags(monkeypatch):
    # Default all feature flags OFF for each test to prevent env leakage.
    for k in (
        "EXTRACTOR_SCI",
        "EXTRACTOR_BIO",
        "EXTRACTOR_TEXT2NKG",
        "TEMPORAL_GRAPH_MODEL",
    ):
        monkeypatch.setenv(k, "0")
    yield
