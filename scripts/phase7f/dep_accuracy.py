#!/usr/bin/env python3
from __future__ import annotations
import os, json, time, glob, collections
from typing import Dict, List, Set, Tuple

SCEN_GLOBS = [
    "docs/phase7f/revocation/scenarios/*.json",
    "data/phase7f/dep_scenarios/*.json",  # fallback if present
]

def cascade_scope(edges: List[Tuple[str,str]], starts: List[str]) -> Set[str]:
    graph = collections.defaultdict(list)
    for u,v in edges: graph[u].append(v)
    scope=set(starts); dq=collections.deque(starts)
    while dq:
        u=dq.popleft()
        for v in graph.get(u, ()):
            if v not in scope:
                scope.add(v); dq.append(v)
    return scope

def cycle_detect(edges: List[Tuple[str,str]]) -> bool:
    graph = collections.defaultdict(list)
    for u,v in edges: graph[u].append(v)
    WHITE,GRAY,BLACK=0,1,2; color=collections.defaultdict(int)
    def dfs(u):
        color[u]=GRAY
        for v in graph[u]:
            if color[v]==GRAY: return True
            if color[v]==WHITE and dfs(v): return True
        color[u]=BLACK; return False
    return any(dfs(u) for u in list(graph.keys()) if color[u]==WHITE)

def evaluate_scenario(path:str)->Dict:
    with open(path) as f: s=json.load(f)
    edges=[tuple(e) for e in s["edges"]]; starts=list(s["starts"])
    expected=set(s["expected_scope"])
    pred=cascade_scope(edges, starts)
    tp=len(pred & expected); fn=len(expected - pred); fp=len(pred - expected)
    precision = tp/len(pred) if pred else 1.0
    recall    = tp/len(expected) if expected else 1.0
    f1 = 0.0 if tp==0 or (precision+recall)==0 else 2*precision*recall/(precision+recall)
    cyc = cycle_detect(edges)
    return {"name":s.get("name","?"),"pred_scope":sorted(pred),"expected_scope":sorted(expected),
            "tp":tp,"fp":fp,"fn":fn,"precision":precision,"recall":recall,"f1":f1,"cycle_detected":cyc}

def main():
    ts=time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir=f"var/receipts/phase7f/dep_acc/{ts}"
    os.makedirs(outdir, exist_ok=True)
    paths=[]
    for pat in SCEN_GLOBS:
        paths.extend(glob.glob(pat))
    paths=sorted(set(paths))
    if not paths:
        raise SystemExit("No scenarios found in docs/phase7f/revocation/scenarios or data/phase7f/dep_scenarios")
    results=[evaluate_scenario(p) for p in paths]
    tp=sum(r["tp"] for r in results); fn=sum(r["fn"] for r in results); fp=sum(r["fp"] for r in results)
    micro_precision = tp/max(1,tp+fp)
    micro_recall    = tp/max(1,tp+fn)  # == dependency_accuracy
    out={"phase":"7F","generated_at_utc":ts,"scenarios":[
            {"name":r["name"],"precision":r["precision"],"recall":r["recall"],"f1":r["f1"],
             "tp":r["tp"],"fp":r["fp"],"fn":r["fn"],"cycle_detected":r["cycle_detected"]} for r in results],
         "micro":{"precision":micro_precision,"recall":micro_recall}}
    with open(os.path.join(outdir,"metrics.json"),"w") as f: json.dump(out,f,indent=2)
    print(os.path.join(outdir,"metrics.json"), end="")
if __name__=="__main__": main()
