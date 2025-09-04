import json, pathlib
from tools.constitutional.report_blocking import summarize

def test_report_shape(tmp_path: pathlib.Path):
    # Create two simple audit rows
    a = tmp_path / "a.jsonl"
    a.write_text(
        '\n'.join([
            json.dumps({"doc_id":"x","stage":"ingest","decision":"ACCEPTABLE","duration_ms":1.2}),
            json.dumps({"doc_id":"y","stage":"ingest","decision":"REJECTED","duration_ms":2.5}),
        ]) + '\n',
        encoding="utf-8"
    )
    rep = summarize([a])
    assert rep["events_total"] == 2
    assert rep["by_decision"]["ACCEPTABLE"] == 1
    assert rep["by_decision"]["REJECTED"] == 1
    assert "ingest" in rep["timing"]
    assert "ACCEPTABLE" in rep["timing"]["ingest"]
    assert "REJECTED" in rep["timing"]["ingest"]
