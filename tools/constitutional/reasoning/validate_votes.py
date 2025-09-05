#!/usr/bin/env python3
import sys, json, argparse, pathlib
try:
    import yaml  # type: ignore
except Exception:
    yaml = None

SCHEMA = json.loads(pathlib.Path(__file__).with_name("operator_vote_schema.json").read_text(encoding="utf-8"))

def load_any(path: str):
    p = pathlib.Path(path)
    text = p.read_text(encoding="utf-8")
    if p.suffix.lower() in (".yaml", ".yml"):
        if not yaml:
            raise RuntimeError("pyyaml not installed")
        return yaml.safe_load(text)
    return json.loads(text)

def validate(obj):
    def req(path, key):
        if key not in path: raise ValueError(f"missing required field: {key}")
    req(obj, "version")
    if obj["version"] != "vote_schema_v1":
        raise ValueError("version must be vote_schema_v1")
    req(obj, "decision_context"); dc = obj["decision_context"]
    req(dc, "id"); req(dc, "description")
    req(obj, "votes")
    if not isinstance(obj["votes"], list) or not obj["votes"]:
        raise ValueError("votes must be non-empty list")
    for v in obj["votes"]:
        for k in ["principle","decision","rationale"]:
            req(v, k)
        if v.get("decision") not in ("ALLOW","DENY","PENDING"):
            raise ValueError("vote.decision invalid")
        w = v.get("weight", 1.0)
        if not (isinstance(w,(int,float)) and 0.0 <= w <= 1.0):
            raise ValueError("vote.weight out of range")
    return True

def resolve(obj):
    if any(v.get("decision") == "DENY" for v in obj["votes"]):
        return {"resolution": "REJECTED", "basis": "DENY precedence"}
    allow_mass = sum(v.get("weight",1.0) for v in obj["votes"] if v.get("decision")=="ALLOW")
    if allow_mass >= 0.5:
        return {"resolution": "ACCEPTABLE", "basis": f"allow_mass={allow_mass:.3f} >= 0.5"}
    return {"resolution": "PENDING", "basis": f"allow_mass={allow_mass:.3f} < 0.5"}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file", help="vote file (.yaml/.json)")
    ap.add_argument("--print", dest="dump", action="store_true", help="print normalized input")
    args = ap.parse_args()
    obj = load_any(args.file)
    validate(obj)
    out = {"ok": True, "decision_context": obj["decision_context"], **resolve(obj)}
    if args.dump:
        out["input"] = obj
    print(json.dumps(out, indent=2))
if __name__ == "__main__":
    main()
