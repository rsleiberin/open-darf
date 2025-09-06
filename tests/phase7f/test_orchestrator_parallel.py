import json, subprocess, pathlib, sys, os, tempfile
def run(cmd):
    return subprocess.check_output(cmd, text=True)
def test_parallel_orchestrator_receipt_and_deny():
    with tempfile.TemporaryDirectory() as td:
        c = pathlib.Path(td)/"constraints.json"
        c.write_text(json.dumps({"deny":["docE"]}))
        out = run(["scripts/phase7f/synthesis_orchestrator_parallel.py","--constraints",str(c)])
        p = pathlib.Path(out.strip()); assert p.exists()
        data = json.loads(p.read_text())
        docs = [d for d,_ in data["fused_topk"]]
        assert "docE" not in docs
        assert data["timing_sec"] >= 0.0
