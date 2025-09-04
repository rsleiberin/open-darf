import json, tempfile, pathlib, io, sys
from tools.constitutional.document_tagger import main as tag_main

def write_jsonl(path, rows):
    with open(path, "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")

def test_tagger_rules(tmp_path: pathlib.Path):
    docs = [
        {"id":"a","text":"", "source":"x"},
        {"id":"b","text":"short","source":"x"},
        {"id":"c","text":"ok "*20, "source":"blockedSite"},
        {"id":"d","text":"ok "*20, "source":"goodSource"},
    ]
    inp = tmp_path/"docs.jsonl"
    out = tmp_path/"tags.jsonl"
    write_jsonl(inp, docs)
    rc = tag_main(["--in", str(inp), "--out-tags", str(out), "--blocklist", "blocked"])
    assert rc == 0
    tags = [json.loads(x) for x in out.read_text().splitlines()]
    m = {t["id"]: t["decision"] for t in tags}
    assert m["a"] == "REJECTED"
    assert m["b"] == "REJECTED"
    assert m["c"] == "REJECTED"
    assert m["d"] == "ACCEPTABLE"
