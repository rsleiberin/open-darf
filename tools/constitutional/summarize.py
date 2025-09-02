import os, json, glob, statistics
from typing import Dict, Any, List

def summarize_audits(run_dir: str) -> Dict[str, Any]:
    path = os.path.join(run_dir, "audit.jsonl")
    out = {"path": run_dir, "calls": 0, "states": {}, "p50_us": 0.0, "p95_us": 0.0, "p99_us": 0.0, "explanations_sample": []}
    if not os.path.exists(path):
        return out
    lat = []
    exps = []
    states = {}
    with open(path, "r", encoding="utf-8") as f:
        for i, line in enumerate(f):
            try:
                obj = json.loads(line)
            except Exception:
                continue
            s = obj.get("state","INDETERMINATE")
            states[s] = states.get(s, 0) + 1
            lat.append(float(obj.get("elapsed_us", 0.0)))
            for p in obj.get("principles", []):
                if isinstance(p, str) and p.startswith("exp:") and len(exps) < 5:
                    exps.append(p)
    out["calls"] = sum(states.values())
    out["states"] = states
    if lat:
        lat_s = sorted(lat)
        def pct(v, p):
            if not v: return 0.0
            k=max(0, min(len(v)-1, int(len(v)*p)))
            return v[k]
        out["p50_us"] = pct(lat_s, 0.50)
        out["p95_us"] = pct(lat_s, 0.95)
        out["p99_us"] = pct(lat_s, 0.99)
    out["explanations_sample"] = exps
    return out

def write_rollup(root="var/receipts/phase7a/text2nkg"):
    runs = [d for d in glob.glob(os.path.join(root, "*_*_*")) if os.path.isdir(d)]
    roll = [summarize_audits(d) for d in sorted(runs)]
    return roll

if __name__ == "__main__":
    roll = write_rollup()
    outp = "var/receipts/phase7a/constitutional/audit_summarized.json"
    os.makedirs(os.path.dirname(outp), exist_ok=True)
    with open(outp, "w") as f:
        json.dump(roll, f, indent=2)
    print(outp)
