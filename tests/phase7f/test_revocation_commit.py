import json, subprocess, pathlib, os, tempfile

def write_json(p, obj):
    with open(p,"w") as f: json.dump(obj,f)

def test_commit_guarded_dry_run(tmp_path):
    plan = {
        "cascade_scope_sorted": ["Y","Z"]
    }
    plan_path = tmp_path/"revocation_plan.json"
    write_json(plan_path, plan)

    exe = pathlib.Path("scripts/phase7f/revocation_commit.py").as_posix()
    env = os.environ.copy()
    # Ensure dry-run
    env.pop("NEO4J_URI", None); env.pop("NEO4J_USER", None); env.pop("NEO4J_PASS", None)
    env.pop("QDRANT_URL", None); env.pop("QDRANT_COLLECTION", None)
    env["APPLY"] = "0"

    out = subprocess.check_output([exe, "--plan", plan_path.as_posix()], text=True, env=env).strip()
    assert out.endswith("commit_receipt.json")
    data = json.load(open(out,"r"))
    assert data["phase"] == "7F"
    assert data["mode"] == "revocation_commit"
    # Both backends skipped in dry-run without env
    assert data["results"]["neo4j"].get("skipped") is True
    assert data["results"]["qdrant"].get("skipped") is True
