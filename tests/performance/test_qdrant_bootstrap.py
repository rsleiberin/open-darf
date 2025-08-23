import statistics
import time

from tools.qdrant_bootstrap import VectorConfig, collection_config, ensure_collection


class _StubQdrant:
    def __init__(self):
        self._collections = {}

    def get_collection(self, name: str):
        if name not in self._collections:
            raise KeyError(name)
        return {"status": "green", "config": self._collections[name]}

    def create_collection(self, *, collection_name: str, vectors_config):
        self._collections[collection_name] = {
            "vectors": dict(vectors_config),
            "on_disk": True,
        }


def test_collection_config_shape():
    cfg = collection_config("anchors", vec=VectorConfig(size=1024, distance="Cosine"))
    assert cfg["name"] == "anchors"
    assert cfg["vectors"]["size"] == 1024
    assert cfg["vectors"]["distance"] == "Cosine"
    assert cfg["on_disk"] is True


def test_ensure_collection_idempotent_and_fast():
    client = _StubQdrant()
    created, out = ensure_collection(
        client, "anchors", vec=VectorConfig(1024, "Cosine")
    )
    assert created is True
    assert out["ok"] is True
    assert out["created"] is True

    # Second call should be no-op and fast
    created2, out2 = ensure_collection(
        client, "anchors", vec=VectorConfig(1024, "Cosine")
    )
    assert created2 is False
    assert out2["ok"] is True
    assert out2.get("existing") is True

    # Microbench: repeated ensure when present should be very fast
    durations = []
    for _ in range(250):
        t0 = time.perf_counter()
        ensure_collection(client, "anchors", vec=VectorConfig(1024, "Cosine"))
        durations.append((time.perf_counter() - t0) * 1e3)  # ms

    p95 = sorted(durations)[int(len(durations) * 0.95)]
    avg = statistics.fmean(durations)
    # Gentle gates: keep far below our 10ms Qdrant budget for a pure no-op
    assert p95 < 10.0, f"p95 too high: {p95} ms"
    assert avg < 3.0, f"avg too high: {avg} ms"
