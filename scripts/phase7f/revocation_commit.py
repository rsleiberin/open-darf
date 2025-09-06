#!/usr/bin/env python3
"""
Phase 7F — Revocation Commit Executor (guarded)
- Input: revocation_plan.json produced by revocation_planner.py
- Behavior:
    * Default DRY-RUN (no external mutations).
    * If APPLY=1 and {NEO4J_URI, NEO4J_USER, NEO4J_PASS} set and cypher-shell available:
        - Delete Document nodes by id from Neo4j (DETACH DELETE).
    * If QDRANT_URL set, note intended vector deletion (no-op unless APPLY=1 and curl present).
- Output: commit_receipt.json under var/receipts/phase7f/revocation_commit/<ts>/
"""
import argparse, json, os, time, pathlib, shutil, subprocess, sys

def have(exe: str) -> bool:
    from shutil import which
    return which(exe) is not None

def read_json(path: str):
    with open(path,"r") as f: return json.load(f)

def neo4j_delete(ids, env, outdir, apply: bool):
    uri, user, pwd = env["NEO4J_URI"], env["NEO4J_USER"], env["NEO4J_PASS"]
    cypher = "UNWIND $ids AS id MATCH (d:Document {id:id}) DETACH DELETE d;"
    cmd = ["cypher-shell", "-a", uri, "-u", user, "-p", pwd, "-param", "ids:"+json.dumps(ids), cypher]
    if apply:
        try:
            res = subprocess.run(cmd, check=True, capture_output=True, text=True)
            open(os.path.join(outdir,"neo4j_apply.out"),"w").write(res.stdout)
            return {"applied": True, "count": len(ids)}
        except subprocess.CalledProcessError as e:
            open(os.path.join(outdir,"neo4j_apply.err"),"w").write(e.stderr)
            return {"applied": False, "error": "cypher-shell failed"}
    else:
        open(os.path.join(outdir,"neo4j_dryrun.cql"),"w").write(cypher)
        return {"applied": False, "dry_run": True, "count": len(ids)}

def qdrant_delete(ids, env, outdir, apply: bool):
    url = env.get("QDRANT_URL","")
    collection = env.get("QDRANT_COLLECTION","documents")
    payload = {"points": ids}
    req = f"DELETE {url}/collections/{collection}/points?wait=true"
    if apply and have("curl") and url:
        try:
            res = subprocess.run(["curl","-sS","-X","DELETE", f"{url}/collections/{collection}/points?wait=true",
                                  "-H","Content-Type: application/json","-d",json.dumps(payload)],
                                  check=True, capture_output=True, text=True)
            open(os.path.join(outdir,"qdrant_apply.json"),"w").write(res.stdout)
            return {"applied": True, "count": len(ids)}
        except subprocess.CalledProcessError as e:
            open(os.path.join(outdir,"qdrant_apply.err"),"w").write(e.stderr)
            return {"applied": False, "error":"qdrant curl failed"}
    else:
        open(os.path.join(outdir,"qdrant_dryrun.json"),"w").write(json.dumps({"request": req, "body": payload}, indent=2))
        return {"applied": False, "dry_run": True, "count": len(ids)}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--plan", required=True, help="Path to revocation_plan.json")
    ap.add_argument("--outdir", default="")
    args = ap.parse_args()

    plan = read_json(args.plan)
    ids = plan.get("cascade_scope_sorted", [])
    ts = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir = args.outdir or os.path.join("var","receipts","phase7f","revocation_commit", ts)
    pathlib.Path(outdir).mkdir(parents=True, exist_ok=True)

    apply = os.environ.get("APPLY","0") == "1"
    env = {
        "NEO4J_URI": os.environ.get("NEO4J_URI",""),
        "NEO4J_USER": os.environ.get("NEO4J_USER",""),
        "NEO4J_PASS": os.environ.get("NEO4J_PASS",""),
        "QDRANT_URL": os.environ.get("QDRANT_URL",""),
        "QDRANT_COLLECTION": os.environ.get("QDRANT_COLLECTION","documents")
    }

    results = {"applied": apply, "neo4j": None, "qdrant": None}

    # Neo4j path
    if shutil.which("cypher-shell") and env["NEO4J_URI"] and env["NEO4J_USER"] and env["NEO4J_PASS"]:
        results["neo4j"] = neo4j_delete(ids, env, outdir, apply)
    else:
        open(os.path.join(outdir,"neo4j_skipped.txt"),"w").write("missing env or cypher-shell")
        results["neo4j"] = {"skipped": True}

    # Qdrant path (optional)
    if env["QDRANT_URL"]:
        results["qdrant"] = qdrant_delete(ids, env, outdir, apply)
    else:
        open(os.path.join(outdir,"qdrant_skipped.txt"),"w").write("QDRANT_URL not set")
        results["qdrant"] = {"skipped": True}

    receipt = {
        "phase":"7F",
        "mode":"revocation_commit",
        "plan_path": args.plan,
        "ids": ids,
        "results": results
    }
    with open(os.path.join(outdir,"commit_receipt.json"),"w") as f:
        json.dump(receipt,f,indent=2)
    print(os.path.join(outdir,"commit_receipt.json"))

if __name__ == "__main__":
    main()
