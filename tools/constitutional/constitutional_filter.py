from __future__ import annotations
import argparse, json, sys
from typing import Dict, Any, Iterator
from .tri_state import TriState
from .audit import AuditEvent, Timer

def load_jsonl(path: str) -> Iterator[Dict[str, Any]]:
    with (sys.stdin if path == "-" else open(path, "r", encoding="utf-8")) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)

def tag_map(tags_path: str) -> Dict[str, str]:
    m: Dict[str, str] = {}
    for t in load_jsonl(tags_path):
        m[str(t.get("id"))] = str(t.get("decision"))
    return m

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Constitutional Filter (fail-closed)")
    ap.add_argument("--in", dest="in_path", required=True, help="Input JSONL docs")
    ap.add_argument("--tags", dest="tags_path", required=True, help="TriState tags JSONL")
    ap.add_argument("--out-accepted", dest="out_ok", required=True, help="Output JSONL of accepted docs")
    ap.add_argument("--audit-stdout", action="store_true")
    args = ap.parse_args(argv)

    decisions = tag_map(args.tags_path)
    accepted = rejected = pending = 0

    with open(args.out_ok, "w", encoding="utf-8") as fo:
        for doc in load_jsonl(args.in_path):
            did = str(doc.get("id") or doc.get("doc_id") or "")
            with Timer() as tmr:
                dec = decisions.get(did, TriState.PENDING.value)  # fail-closed unknowns
                if dec == TriState.ACCEPTABLE.value:
                    fo.write(json.dumps(doc, ensure_ascii=False) + "\n")
                    accepted += 1
                    ev = AuditEvent(doc_id=did, stage="ingest", decision=TriState.ACCEPTABLE, rule_id="FILTER_PASS", rationale="accepted by TriState")
                elif dec == TriState.REJECTED.value:
                    rejected += 1
                    ev = AuditEvent(doc_id=did, stage="ingest", decision=TriState.REJECTED, rule_id="FILTER_BLOCK", rationale="blocked by TriState")
                else:
                    pending += 1
                    ev = AuditEvent(doc_id=did, stage="ingest", decision=TriState.PENDING, rule_id="FILTER_FAIL_CLOSED", rationale="unknown tag → pending (blocked)")
            ev.duration_ms = tmr.elapsed_ms
            if args.audit_stdout:
                sys.stdout.write(json.dumps(ev.to_dict(), ensure_ascii=False) + "\n")

    print(json.dumps({"accepted": accepted, "rejected": rejected, "pending": pending}, ensure_ascii=False))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
