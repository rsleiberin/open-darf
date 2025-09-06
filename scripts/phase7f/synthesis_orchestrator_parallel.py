#!/usr/bin/env python3
import os, json, time, argparse, concurrent.futures, pathlib
from typing import List, Tuple

def rrf_fuse(vec: List[Tuple[str,float]], gra: List[Tuple[str,float]], k:int=60):
    ranks = {}
    for i,(d,_s) in enumerate(vec, start=1):
        ranks[d] = ranks.get(d, 0.0) + 1.0/(k+i)
    for i,(d,_s) in enumerate(gra, start=1):
        ranks[d] = ranks.get(d, 0.0) + 1.0/(k+i)
    return sorted(ranks.items(), key=lambda x: -x[1])

def load_ranked_from_json(path, key):
    with open(path) as f:
        obj=json.load(f)
    arr = obj.get(key) or []
    return [(d,s) for d,s in arr]

def stub_vector():
    time.sleep(0.005); return [("docA",0.82),("docB",0.77),("docC",0.55),("docD",0.31)]
def stub_graph():
    time.sleep(0.004); return [("docB",3),("docE",2),("docA",1)]

def run_vector(path):
    if path and os.path.exists(path): return load_ranked_from_json(path,"vector_ranked")
    # TODO: real Qdrant if env present
    return stub_vector()

def run_graph(path):
    if path and os.path.exists(path): return load_ranked_from_json(path,"graph_ranked")
    # TODO: real Neo4j if env present
    return stub_graph()

def apply_constraints(fused, constraints_path:str):
    if not constraints_path: return fused
    try:
        with open(constraints_path) as f: c=json.load(f)
        deny=set(c.get("deny",[]))
        if not deny: return fused
        return [(d,s) for d,s in fused if d not in deny]
    except Exception:
        # fail-closed on constraint errors
        return []

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--vector-json", default="")
    ap.add_argument("--graph-json", default="")
    ap.add_argument("--constraints", default="")
    ap.add_argument("--topk", type=int, default=5)
    ap.add_argument("--rrf-k", type=int, default=60)
    args=ap.parse_args()

    t0=time.perf_counter()
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
        fv=ex.submit(run_vector, args.vector_json)
        fg=ex.submit(run_graph,  args.graph_json)
        vec=fv.result(); gra=fg.result()
    fused = rrf_fuse(vec, gra, k=args.rrf_k)
    fused = apply_constraints(fused, args.constraints)
    fused = fused[:args.topk]
    t1=time.perf_counter()

    ts=time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir=pathlib.Path(f"var/receipts/phase7f/orchestrator_parallel/{ts}")
    outdir.mkdir(parents=True, exist_ok=True)
    out={
        "phase":"7F","mode":"orchestrator_parallel","rrf_k":args.rrf_k,"topk":args.topk,
        "vector_path":args.vector_json or "<stub>","graph_path":args.graph_json or "<stub>",
        "constraints_path":args.constraints or "<none>","timing_sec":round(t1-t0,6),
        "fused_topk": fused
    }
    (outdir/"summary.json").write_text(json.dumps(out, indent=2))
    print(outdir/"summary.json")

if __name__=="__main__":
    main()
