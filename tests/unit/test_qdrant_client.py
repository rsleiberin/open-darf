from apps.anchors.qdrant_client import QdrantWrapper, QdrantConfig


class FakeQdrant:
    def __init__(self):
        self.collections = {}
        self.upserts = []

    # simulate get_collection / create_collection
    def get_collection(self, name):
        if name not in self.collections:
            raise RuntimeError("not found")
        return self.collections[name]

    def create_collection(self, collection_name, vectors_config):
        self.collections[collection_name] = {"vectors_config": vectors_config}

    # simulate upsert
    def upsert(self, collection_name, points):
        assert (
            collection_name in self.collections
        ), "collection must exist before upsert"
        assert {"ids", "vectors", "payloads"} <= set(points.keys())
        n = len(points["ids"])
        assert n == len(points["vectors"]) == len(points["payloads"])
        self.upserts.append((collection_name, n))


def test_ensure_collection_idempotent():
    fake = FakeQdrant()
    wrap = QdrantWrapper(fake)
    cfg = QdrantConfig(
        url="http://fake", collection="anchors", vector_size=8, distance="Cosine"
    )
    wrap.ensure_collection(cfg)
    # second call must not raise and must not overwrite
    wrap.ensure_collection(cfg)
    assert "anchors" in fake.collections
    assert fake.collections["anchors"]["vectors_config"]["size"] == 8


def test_upsert_points_ok():
    fake = FakeQdrant()
    wrap = QdrantWrapper(fake)
    cfg = QdrantConfig(url="http://fake", collection="anchors", vector_size=4)
    wrap.ensure_collection(cfg)
    pts = [
        ("a", [0.1, 0.2, 0.3, 0.4], {"doc": "d1", "pos": 0}),
        ("b", [0.2, 0.3, 0.4, 0.5], {"doc": "d1", "pos": 1}),
    ]
    n = wrap.upsert(cfg.collection, pts)
    assert n == 2
    assert fake.upserts and fake.upserts[-1] == ("anchors", 2)
