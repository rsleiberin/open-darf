from __future__ import annotations
import argparse, json, sys
from typing import Dict, Iterator

ALLOWED = {"ACCEPTABLE"}

def load_jsonl(path: str) -> Iterator[dict]:
    with open(path, "r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)

def tag_map(path: str) -> Dict[str, str]:
    m: Dict[str,str] = {}
    for t in load_jsonl(path):
        did = str(t.get("id") or t.get("doc_id") or "")
        dec = str(t.get("decision") or "").upper()
        if did:
            m[did] = dec
    return m

def keep(decisions: Dict[str,str], did: str) -> bool:
    dec = decisions.get(str(did), "PENDING").upper()
    return dec in ALLOWED

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Gate nodes/edges by TriState tags (fail-closed)")
    ap.add_argument("--nodes-in", required=True)
    ap.add_argument("--edges-in", required=True)
    ap.add_argument("--tags", required=True)
    ap.add_argument("--nodes-out", required=True)
    ap.add_argument("--edges-out", required=True)
    ap.add_argument("--audit-stdout", action="store_true")
    args = ap.parse_args(argv)

    decisions = tag_map(args.tags)

    kept_nodes = kept_edges = dropped_nodes = dropped_edges = 0

    with open(args.nodes_out, "w", encoding="utf-8") as no:
        for n in load_jsonl(args.nodes_in):
            did = n.get("doc_id") or n.get("id") or ""
            if keep(decisions, did):
                kept_nodes += 1
                no.write(json.dumps(n, ensure_ascii=False) + "\n")
                if args.audit_stdout:
                    sys.stdout.write(json.dumps({"stage":"kg","object":"node","doc_id":did,"decision":"ACCEPTABLE"})+"\n")
            else:
                dropped_nodes += 1
                if args.audit_stdout:
                    sys.stdout.write(json.dumps({"stage":"kg","object":"node","doc_id":did,"decision":"REJECTED"})+"\n")

    with open(args.edges_out, "w", encoding="utf-8") as eo:
        for e in load_jsonl(args.edges_in):
            did = e.get("doc_id") or e.get("id") or ""
            if keep(decisions, did):
                kept_edges += 1
                eo.write(json.dumps(e, ensure_ascii=False) + "\n")
                if args.audit_stdout:
                    sys.stdout.write(json.dumps({"stage":"kg","object":"edge","doc_id":did,"decision":"ACCEPTABLE"})+"\n")
            else:
                dropped_edges += 1
                if args.audit_stdout:
                    sys.stdout.write(json.dumps({"stage":"kg","object":"edge","doc_id":did,"decision":"REJECTED"})+"\n")

    print(json.dumps({
        "nodes_kept": kept_nodes, "nodes_dropped": dropped_nodes,
        "edges_kept": kept_edges, "edges_dropped": dropped_edges
    }, ensure_ascii=False))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
