import json, pathlib, subprocess, sys

def write_jsonl(p, rows):
    with open(p, "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")

def test_gate_spans(tmp_path: pathlib.Path):
    spans = [
        {"doc_id":"a","start":0,"end":3,"label":"X"},
        {"doc_id":"b","start":1,"end":4,"label":"Y"},
        {"doc_id":"c","start":2,"end":5,"label":"Z"},
    ]
    tags  = [{"id":"a","decision":"ACCEPTABLE"},{"id":"b","decision":"REJECTED"}]  # 'c' => PENDING => blocked

    sin, tin, sout = tmp_path/"spans.jsonl", tmp_path/"tags.jsonl", tmp_path/"spans.ok.jsonl"
    write_jsonl(sin, spans); write_jsonl(tin, tags)

    rc = subprocess.call([sys.executable, "-m", "tools.constitutional.gate_spans",
                          "--spans-in", str(sin), "--tags", str(tin), "--spans-out", str(sout)])
    assert rc == 0
    kept = [json.loads(x) for x in sout.read_text().splitlines()]
    assert [s["doc_id"] for s in kept] == ["a"]
