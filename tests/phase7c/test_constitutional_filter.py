import json, pathlib
from tools.constitutional.constitutional_filter import main as filt_main

def write_jsonl(path, rows):
    with open(path, "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")

def test_filter_fail_closed(tmp_path: pathlib.Path):
    # Prepare sample docs and tags; 'c' is intentionally untagged to verify fail-closed PENDING blocking
    docs = [{"id":"a","text":"ok text"}, {"id":"b","text":"ok text"}, {"id":"c","text":"ok text"}]
    tags = [{"id":"a","decision":"ACCEPTABLE"},{"id":"b","decision":"REJECTED"}]
    inp = tmp_path/"docs.jsonl"
    tagp = tmp_path/"tags.jsonl"
    out = tmp_path/"ok.jsonl"
    write_jsonl(inp, docs)
    write_jsonl(tagp, tags)
    rc = filt_main(["--in", str(inp), "--tags", str(tagp), "--out-accepted", str(out)])
    assert rc == 0
    accepted = [json.loads(x) for x in out.read_text().splitlines()]
    assert [d["id"] for d in accepted] == ["a"]  # only ACCEPTABLE passes
