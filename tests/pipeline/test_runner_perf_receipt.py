import json
import os
import pathlib
from apps.pipeline.ingest.local import LocalFSIngest
from apps.pipeline.run import run_once


def test_runner_perf_obs_receipt(tmp_path: pathlib.Path, monkeypatch):
    # Prepare sample files
    root = tmp_path / "in"
    (root / "nested").mkdir(parents=True, exist_ok=True)
    (root / "a.txt").write_text("alpha")
    (root / "nested" / "b.txt").write_text("beta")

    # Enable perf/obs
    monkeypatch.setenv("PIPELINE_PERF", "1")

    count, path = run_once(LocalFSIngest(str(root)), bucket="pipeline_perf")
    assert count == 2 and os.path.isfile(path)

    data = json.loads(pathlib.Path(path).read_text())
    assert data["count"] == 2
    assert "perf" in data and "obs" in data
    assert (
        set(data["obs"]["parser_counts"].values()) == {1, 2}
        or sum(data["obs"]["parser_counts"].values()) == 2
    )
    for sec in ("parse_ms", "process_ms"):
        for k in ("p50", "p95", "max", "avg", "n"):
            assert k in data["perf"][sec]
