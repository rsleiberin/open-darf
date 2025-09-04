import json, pathlib, subprocess, sys

def write_jsonl(p, rows):
    with open(p, "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")

def test_gate_nodes_edges(tmp_path: pathlib.Path):
    nodes = [{"doc_id":"a","n":1},{"doc_id":"b","n":2},{"doc_id":"c","n":3}]
    edges = [{"doc_id":"a","e":1},{"doc_id":"b","e":2},{"doc_id":"c","e":3}]
    tags  = [{"id":"a","decision":"ACCEPTABLE"},{"id":"b","decision":"REJECTED"}]  # 'c' => PENDING => blocked

    nin, ein, tin = tmp_path/"nodes.jsonl", tmp_path/"edges.jsonl", tmp_path/"tags.jsonl"
    nout, eout = tmp_path/"nodes.ok.jsonl", tmp_path/"edges.ok.jsonl"
    write_jsonl(nin, nodes); write_jsonl(ein, edges); write_jsonl(tin, tags)

    rc = subprocess.call([sys.executable, "-m", "tools.constitutional.gate_nodes_edges",
                          "--nodes-in", str(nin), "--edges-in", str(ein),
                          "--tags", str(tin), "--nodes-out", str(nout), "--edges-out", str(eout)])
    assert rc == 0
    kept_nodes = [json.loads(x) for x in nout.read_text().splitlines()]
    kept_edges = [json.loads(x) for x in eout.read_text().splitlines()]
    assert [n["doc_id"] for n in kept_nodes] == ["a"]
    assert [e["doc_id"] for e in kept_edges] == ["a"]
