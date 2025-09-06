import json, os, subprocess, sys, tempfile, pathlib

def write_json(path, obj):
    with open(path,"w") as f: json.dump(obj,f)

def test_rrf_fusion_and_constraints(tmp_path):
    # Prepare synthetic vector & graph rankings
    vec = {"vector_ranked":[["docA",0.82],["docB",0.77],["docC",0.55],["docD",0.31]]}
    gra = {"graph_ranked":[["docB",3],["docE",2],["docA",1]]}
    constraints = [["docA","docE"]]  # forbid co-occurrence

    v = tmp_path/"vector.json"; g = tmp_path/"graph.json"; c = tmp_path/"constraints.json"
    write_json(v, vec); write_json(g, gra); write_json(c, constraints)

    # Run orchestrator
    exe = pathlib.Path("scripts/phase7f/synthesis_orchestrator.py").as_posix()
    out = subprocess.check_output([exe, "--vector", v.as_posix(), "--graph", g.as_posix(), "--constraints", c.as_posix(), "--topk","5"], text=True).strip()
    assert out.endswith("fused.json")
    with open(out, "r") as f:
        data = json.load(f)

    # Basic shape
    assert data["phase"] == "7F"
    fused = data["fused_topk"]
    # docB should lead (strong in both signals)
    assert fused[0][0] == "docB"
    # docA and docE co-occur; one is demoted to 0.0 by constraint demotion
    scores = {d:s for d,s in fused}
    assert scores["docA"] == 0.0 or scores.get("docE",0.0) == 0.0
