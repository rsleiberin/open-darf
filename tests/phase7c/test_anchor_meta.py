import json, pathlib, subprocess, sys

def write_jsonl(p, rows):
    with open(p, "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")

def read_jsonl(p):
    return [json.loads(x) for x in open(p, "r", encoding="utf-8").read().splitlines()]

def test_anchor_meta_roundtrip(tmp_path: pathlib.Path):
    tags = [
        {"id":"a","decision":"ACCEPTABLE","rule_id":"PASS_RULES","rationale":"ok"},
        {"id":"b","decision":"REJECTED","rule_id":"TOO_SHORT","rationale":"len<min"},
    ]
    t = tmp_path/"tags.jsonl"
    out = tmp_path/"meta.jsonl"
    write_jsonl(t, tags)
    rc = subprocess.call([sys.executable, "-m", "tools.constitutional.anchor_meta",
                          "--tags", str(t), "--out", str(out)])
    assert rc == 0
    rows = read_jsonl(out)
    m = {r["id"]: r for r in rows}
    assert m["a"]["constitutional_status"] == "ACCEPTABLE"
    assert m["a"]["constitutional_rule_id"] == "PASS_RULES"
    assert m["b"]["constitutional_status"] == "REJECTED"
    assert m["b"]["constitutional_rationale"] == "len<min"
