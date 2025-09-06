#!/usr/bin/env python3
"""
Phase 7F — Synthesis Orchestrator (read-only)
- Inputs: vector JSON, graph JSON (each list of [doc_id, score_or_rank])
- Fusion: RRF(k=60) over both rankings
- Constitutional filter: drop pairs explicitly violating a simple "may_not_coexist_with" constraint list (optional)
- Output: fused_topk JSON receipt under var/receipts/phase7f/orchestrator_run/<ts>/fused.json
"""
import argparse, json, os, time, pathlib
from typing import List, Tuple, Dict, Any

def load_rank_list(path: str) -> List[Tuple[str, float]]:
    with open(path, "r") as f:
        data = json.load(f)
    # Support two shapes: {"items":[["doc",score],...]} or raw list
    if isinstance(data, dict) and "items" in data:
        items = data["items"]
    else:
        # Allow our prior receipts where the ranking is stored under keys "vector_ranked" / "graph_ranked"
        if "vector_ranked" in data:
            items = data["vector_ranked"]
        elif "graph_ranked" in data:
            items = data["graph_ranked"]
        else:
            items = data
    # Normalize to [(doc,score_float)]
    out = []
    for row in items:
        if isinstance(row, (list, tuple)) and len(row) >= 2:
            doc, val = row[0], row[1]
            try:
                score = float(val)
            except Exception:
                # if the second column is rank (int), invert to score-ish
                score = 1.0/float(val) if isinstance(val, int) else 0.0
            out.append((str(doc), score))
    return out

def rrf(ranked: List[Tuple[str, float]], k: int = 60) -> Dict[str, float]:
    # Sort descending by score; assign 1/(k+rank_index)
    ranked_sorted = sorted(ranked, key=lambda t: t[1], reverse=True)
    return {doc: 1.0/(k+i) for i,(doc,_) in enumerate(ranked_sorted, start=1)}

def fuse_rrf(vec: List[Tuple[str,float]], gra: List[Tuple[str,float]], k: int = 60) -> Dict[str,float]:
    r_vec, r_gra = rrf(vec, k), rrf(gra, k)
    docs = set(d for d,_ in vec) | set(d for d,_ in gra)
    return {d: r_vec.get(d,0.0) + r_gra.get(d,0.0) for d in docs}

def apply_constraints(cands: List[Tuple[str,float]], constraints: List[Tuple[str,str]]) -> List[Tuple[str,float]]:
    forbidden = set(tuple(sorted(pair)) for pair in constraints)
    keep = []
    ids = [d for d,_ in cands]
    # If a forbidden pair co-occurs in the set, demote the latter item by zeroing its score
    for doc,score in cands:
        violated = any(tuple(sorted((doc, other))) in forbidden for other in ids if other != doc)
        keep.append((doc, 0.0 if violated else score))
    # Re-sort after demotion
    keep.sort(key=lambda t: t[1], reverse=True)
    return keep

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--vector", required=True, help="Path to vector ranking JSON")
    ap.add_argument("--graph", required=True, help="Path to graph ranking JSON")
    ap.add_argument("--constraints", default="", help="Path to constraints JSON (optional: list of [a,b] pairs)")
    ap.add_argument("--topk", type=int, default=10)
    ap.add_argument("--rrf_k", type=int, default=60)
    ap.add_argument("--outdir", default="")
    args = ap.parse_args()

    vec = load_rank_list(args.vector)
    gra = load_rank_list(args.graph)
    fused = fuse_rrf(vec, gra, k=args.rrf_k)
    fused_sorted = sorted(fused.items(), key=lambda t:t[1], reverse=True)
    if args.constraints:
        try:
            with open(args.constraints,"r") as f:
                cons = json.load(f)
            constraints = [tuple(x) for x in cons]
        except Exception:
            constraints = []
        fused_sorted = apply_constraints(fused_sorted, constraints)

    ts = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir = args.outdir or os.path.join("var","receipts","phase7f","orchestrator_run", ts)
    pathlib.Path(outdir).mkdir(parents=True, exist_ok=True)
    out = {
        "phase":"7F",
        "mode":"orchestrator_fusion",
        "rrf_k": args.rrf_k,
        "topk": args.topk,
        "vector_path": args.vector,
        "graph_path": args.graph,
        "constraints_path": args.constraints or None,
        "fused_topk": fused_sorted[:args.topk]
    }
    with open(os.path.join(outdir,"fused.json"),"w") as f:
        json.dump(out,f,indent=2)
    print(os.path.join(outdir,"fused.json"))

if __name__ == "__main__":
    main()

# --- 7F/D16: Tri-state enforcement helper (append-only) ---
try:
    from scripts.phase7f.tri_state import Decision, decide_with_constraints, combine_decisions
except Exception:  # fallback to minimal shim
    class Decision(str):
        ALLOW="ALLOW"; DENY="DENY"; INDETERMINATE="INDETERMINATE"
    def decide_with_constraints(scores, constraints):
        # conservative: any False -> DENY; any None -> INDETERMINATE; else ALLOW
        vals = list(constraints.values())
        if any(v is False for v in vals): 
            return "DENY", {"constraints": constraints, "scores": scores}
        if any(v is None for v in vals):
            return "INDETERMINATE", {"constraints": constraints, "scores": scores}
        return "ALLOW", {"constraints": constraints, "scores": scores}
    def combine_decisions(ds):
        return "DENY" if "DENY" in ds else ("ALLOW" if set(ds)=={"ALLOW"} else "INDETERMINATE")

def orchestrator_triage(scores, constraints):
    """Return (Decision, rationale) with deny precedence & fail-closed behavior."""
    decision, rationale = decide_with_constraints(scores, constraints)
    return decision, rationale
