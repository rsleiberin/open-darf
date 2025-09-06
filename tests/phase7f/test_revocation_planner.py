import json, subprocess, pathlib

def write_json(p, obj):
    with open(p,"w") as f: json.dump(obj,f)

def test_revocation_planner_scope_and_cycle(tmp_path):
    # Graph: X->Y->Z, plus a cycle A->B->A
    edges = {"edges":[["X","Y"],["Y","Z"],["A","B"],["B","A"]]}
    starts = ["Y"]  # revoking Y should cascade to Y,Z

    e = tmp_path/"edges.json"; s = tmp_path/"starts.json"
    write_json(e, edges); write_json(s, starts)

    exe = pathlib.Path("scripts/phase7f/revocation_planner.py").as_posix()
    out = subprocess.check_output([exe, "--edges", e.as_posix(), "--start", s.as_posix()], text=True).strip()
    assert out.endswith("revocation_plan.json")
    data = json.load(open(out,"r"))
    assert data["phase"] == "7F"
    assert data["cycle_detected"] is True  # due to A<->B
    assert data["cascade_scope_sorted"] == ["Y","Z"]
