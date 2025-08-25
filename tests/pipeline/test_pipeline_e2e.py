import os
import pathlib
from apps.pipeline.ingest.local import LocalFSIngest
from apps.pipeline.run import run_once


def test_e2e_localfs_runner_writes_receipt(tmp_path: pathlib.Path):
    root = tmp_path / "in"
    root.mkdir()
    (root / "doc1.txt").write_text("alpha")
    (root / "nested").mkdir()
    (root / "nested" / "doc2.txt").write_text("beta")

    src = LocalFSIngest(str(root))
    count, receipt_path = run_once(src, bucket="pipeline_e2e")
    assert count == 2
    assert os.path.isfile(receipt_path)
