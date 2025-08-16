import os, time
import pytest
from apps.storage.minio_cas import MinioCAS

REQUIRED = ["MINIO_ENDPOINT", "MINIO_ACCESS_KEY", "MINIO_SECRET_KEY", "MINIO_BUCKET"]
pytestmark = pytest.mark.skipif(any(not os.environ.get(v) for v in REQUIRED),
    reason="MINIO_* env not set; source .env.local or run bin/use-env.sh")

def test_put_get_idempotent_and_head():
    c = MinioCAS()
    data = b"hello-cas"
    r1 = c.put_bytes(data, content_type="text/plain")
    r2 = c.put_bytes(data)
    assert r1 == r2
    assert c.exists(r1)
    assert c.get_bytes(r1, verify=True) == data
    h = c.head(r1)
    assert h["size"] == len(data)

def test_stream_and_soft_delete():
    c = MinioCAS()
    data = b"A" * 1024
    r = c.put_bytes(data)
    out = b"".join(list(c.get_stream(r, chunk_size=128, verify=True)))
    assert out == data
    c.delete(r, hard=False)

def test_head_latency_reasonable():
    c = MinioCAS()
    r = c.put_bytes(b"latency-check")
    t0 = time.perf_counter()
    _ = c.head(r)
    ms = (time.perf_counter() - t0) * 1000
    assert ms < 500
