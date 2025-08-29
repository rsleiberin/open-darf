import json
import glob
from importlib import reload


def test_obs_and_perf_jsonl(tmp_path, monkeypatch):
    # Enable both
    monkeypatch.setenv("OBS_ENABLE", "1")
    monkeypatch.setenv("RUN_PERF", "1")
    monkeypatch.setenv("OBS_METRICS_DIR", str(tmp_path))
    # Import modules and call our functions
    from apps.knowledge_graph.temporal_model import parse_timespan
    from apps.extractors.text2nkg_extractor import extract_relations_simple

    # Calls (should create timers & counters)
    parse_timespan("2021-03-15")
    extract_relations_simple("Aspirin treats fever")
    # Trigger atexit snapshot by manual call
    from apps.observability import metrics

    reload(metrics)
    metrics.write_snapshot()
    # Assert files created
    files = list(glob.glob(str(tmp_path / "*.jsonl")))
    assert files, "expected metrics jsonl files"
    # Check snapshot content has our keys
    snap_lines = [p for p in files if p.endswith("_snapshot.jsonl")]
    assert snap_lines
    data = json.loads(
        open(snap_lines[0], "r", encoding="utf-8").read().splitlines()[-1]
    )
    snap = data.get("snapshot", {})
    assert "temporal" in snap.get("avg_seconds", {})
    assert "text2nkg" in snap.get("avg_seconds", {})
