import json, pathlib, subprocess, sys

def write_jsonl(p, rows):
    with open(p, "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")

def test_gallery(tmp_path: pathlib.Path):
    docs = [{"id":"a","text":"ok text"},{"id":"b","text":"bad url http://x.y"},{"id":"c","text":"email t@x.z"}]
    tags = [{"id":"a","decision":"ACCEPTABLE"},{"id":"b","decision":"REJECTED"}]  # c => PENDING
    din, tin, outp = tmp_path/"docs.jsonl", tmp_path/"tags.jsonl", tmp_path/"g.md"
    write_jsonl(din, docs); write_jsonl(tin, tags)
    rc = subprocess.call([sys.executable, "-m", "tools.constitutional.make_blocked_gallery",
                          "--docs", str(din), "--tags", str(tin), "--out", str(outp)])
    assert rc == 0
    s = outp.read_text(encoding="utf-8")
    assert "REJECTED: 1" in s and "PENDING: 1" in s and "ACCEPTABLE: 1" in s
    assert "[url]" in s  # redaction occurred
