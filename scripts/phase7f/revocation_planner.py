#!/usr/bin/env python3
"""
Phase 7F — Revocation Planner (read-only)
- Inputs: graph (edges) and initial revoke IDs
- Edges are directed: A -> B means "B depends on A" (removing A cascades to B)
- Outputs: cascade scope (sorted), cycle_detected flag, graph_size, receipts path
- No datastore mutations (plan-only). Commit steps are left as TODO/placeholder.
"""
import argparse, json, os, time, pathlib
from collections import defaultdict, deque
from typing import List, Tuple, Dict, Set

def load_edges(path: str) -> List[Tuple[str,str]]:
    with open(path, "r") as f:
        data = json.load(f)
    # Accept {"edges":[["A","B"],...]} or raw list
    edges = data.get("edges", data)
    out = []
    for e in edges:
        if isinstance(e, (list, tuple)) and len(e) >= 2:
            out.append((str(e[0]), str(e[1])))
    return out

def has_cycle(edges: List[Tuple[str,str]]) -> bool:
    # Kahn's algorithm for cycle detection
    indeg = defaultdict(int)
    out = defaultdict(list)
    nodes: Set[str] = set()
    for u,v in edges:
        out[u].append(v)
        indeg[v] += 1
        nodes.add(u); nodes.add(v)
    q = deque([n for n in nodes if indeg[n]==0])
    visited = 0
    while q:
        n = q.popleft(); visited += 1
        for w in out[n]:
            indeg[w] -= 1
            if indeg[w]==0: q.append(w)
    return visited != len(nodes) and len(nodes) > 0

def cascade_scope(edges: List[Tuple[str,str]], starts: List[str]) -> List[str]:
    # BFS over dependency fanout using adjacency A->B
    adj = defaultdict(list)
    for u,v in edges:
        adj[u].append(v)
    seen: Set[str] = set()
    dq = deque(starts)
    while dq:
        n = dq.popleft()
        if n in seen: continue
        seen.add(n)
        for w in adj.get(n, []):
            if w not in seen:
                dq.append(w)
    return sorted(seen)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--edges", required=True, help="Path to edges JSON (either {'edges': [[u,v],...]} or raw list)")
    ap.add_argument("--start", required=True, help="Path to JSON list of starting doc IDs to revoke")
    ap.add_argument("--outdir", default="")
    args = ap.parse_args()

    edges = load_edges(args.edges)
    with open(args.start, "r") as f:
        starts = [str(x) for x in json.load(f)]

    cycle = has_cycle(edges)
    scope = cascade_scope(edges, starts)
    nodes = set()
    for u,v in edges:
        nodes.add(u); nodes.add(v)

    ts = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir = args.outdir or os.path.join("var","receipts","phase7f","revocation_run", ts)
    pathlib.Path(outdir).mkdir(parents=True, exist_ok=True)
    out_path = os.path.join(outdir, "revocation_plan.json")
    out = {
        "phase":"7F",
        "mode":"revocation_plan",
        "input_starts": starts,
        "graph_size": {"nodes": len(nodes), "edges": len(edges)},
        "cycle_detected": cycle,
        "cascade_scope_sorted": scope,
        "commit_steps": [
            "NEO4J: MATCH ... DETACH DELETE for nodes in scope (guarded)",
            "QDRANT: delete vectors for scope (guarded)",
            "PROV-O: emit revocation bundle (scope, time, agent)"
        ]
    }
    with open(out_path,"w") as f: json.dump(out, f, indent=2)
    print(out_path)

if __name__ == "__main__":
    main()
