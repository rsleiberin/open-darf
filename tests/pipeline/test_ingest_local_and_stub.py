import os
import pathlib
from apps.pipeline.ingest.local import LocalFSIngest
from apps.pipeline.ingest.minio_stub import MinioIngestStub
from apps.pipeline.receipts import write_receipt


def test_localfs_ingest_lists_and_fetches(tmp_path: pathlib.Path):
    root = tmp_path / "inbound"
    root.mkdir()
    (root / "a.txt").write_text("hello")
    (root / "b/b.txt").parent.mkdir(parents=True, exist_ok=True)
    (root / "b/b.txt").write_text("world")

    src = LocalFSIngest(str(root))
    found = sorted(list(src.list()))
    assert found == ["a.txt", "b/b.txt"]
    assert src.fetch("a.txt") == b"hello"
    assert src.fetch("b/b.txt") == b"world"


def test_minio_stub_prime_and_fetch():
    stub = MinioIngestStub()
    stub.prime([("x/y.txt", b"hi")])
    assert stub.list() == ["x/y.txt"]
    assert stub.fetch("x/y.txt") == b"hi"
    try:
        stub.fetch("missing")
        assert False, "expected FileNotFoundError"
    except FileNotFoundError:
        pass


def test_receipt_writer_creates_file(tmp_path, monkeypatch):
    # place receipts under tmp docs/audit
    monkeypatch.chdir(tmp_path)
    path = write_receipt("pipeline_sanity", "sample", {"ok": True})
    assert os.path.isfile(path)
