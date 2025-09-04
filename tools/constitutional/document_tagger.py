from __future__ import annotations
import argparse, json, sys, re
from typing import Dict, Iterable, Iterator, Any
from .tri_state import TriState
from .audit import AuditEvent, Timer

# Minimal built-in biomedical-agnostic rules:
#  - EMPTY_TEXT: reject if 'text' missing or empty after strip
#  - TOO_SHORT: reject if length < min_len (default 20)
#  - TOO_LONG: reject if length > max_len (default 500000)
#  - BLOCKLIST_SOURCE: reject if source_id/source contains any banned token
#  - Otherwise: ACCEPTABLE
#
# Input: JSONL of per-doc objects: { "id": "...", "text": "...", "source": "...", ... }
# Output tags JSONL: { "id": "...", "decision": "ACCEPTABLE|REJECTED|PENDING", "rule_id": "...", "rationale": "..." }
# Side-effect: writes audits to stdout if --audit-stdout

def load_jsonl(path: str) -> Iterator[Dict[str, Any]]:
    with (sys.stdin if path == "-" else open(path, "r", encoding="utf-8")) as fh:
        for line in fh:
            line = line.strip()
            if not line: 
                continue
            yield json.loads(line)

def decide(doc: Dict[str, Any], min_len: int, max_len: int, blocklist: Iterable[str]) -> Dict[str, str]:
    doc_id = str(doc.get("id") or doc.get("doc_id") or "")
    text = doc.get("text") or ""
    src  = (doc.get("source") or doc.get("source_id") or "")
    if not isinstance(text, str):
        return {"id": doc_id, "decision": TriState.REJECTED.value, "rule_id": "INVALID_TEXT_TYPE", "rationale": "text not a string"}
    if len(text.strip()) == 0:
        return {"id": doc_id, "decision": TriState.REJECTED.value, "rule_id": "EMPTY_TEXT", "rationale": "no content"}
    n = len(text)
    if n < min_len:
        return {"id": doc_id, "decision": TriState.REJECTED.value, "rule_id": "TOO_SHORT", "rationale": f"len={n} < {min_len}"}
    if n > max_len:
        return {"id": doc_id, "decision": TriState.REJECTED.value, "rule_id": "TOO_LONG", "rationale": f"len={n} > {max_len}"}
    if src and any(t for t in blocklist if t and t.lower() in str(src).lower()):
        return {"id": doc_id, "decision": TriState.REJECTED.value, "rule_id": "BLOCKLIST_SOURCE", "rationale": f"source={src}"}
    return {"id": doc_id, "decision": TriState.ACCEPTABLE.value, "rule_id": "PASS_RULES", "rationale": "meets baseline constraints"}

def main(argv=None) -> int:
    p = argparse.ArgumentParser(description="Document Tagger (TriState)")
    p.add_argument("--in", dest="in_path", required=True, help="Input JSONL of documents")
    p.add_argument("--out-tags", dest="out_tags", required=True, help="Output JSONL of decisions")
    p.add_argument("--min-len", type=int, default=20)
    p.add_argument("--max-len", type=int, default=500000)
    p.add_argument("--blocklist", nargs="*", default=[], help="Blocked source tokens")
    p.add_argument("--audit-stdout", action="store_true", help="Emit audit events to stdout")
    args = p.parse_args(argv)

    audits_path = None  # could be extended to write separate audit logs
    count = {"ACCEPTABLE": 0, "REJECTED": 0, "PENDING": 0}

    with open(args.out_tags, "w", encoding="utf-8") as out_f:
        for doc in load_jsonl(args.in_path):
            with Timer() as tmr:
                decision = decide(doc, args.min_len, args.max_len, args.blocklist)
            count[decision["decision"]] = count.get(decision["decision"], 0) + 1
            out_f.write(json.dumps(decision, ensure_ascii=False) + "\n")
            if args.audit_stdout:
                ev = AuditEvent(
                    doc_id=str(doc.get("id") or doc.get("doc_id") or ""),
                    stage="ingest",
                    decision=TriState.from_str(decision["decision"]),
                    rule_id=decision.get("rule_id"),
                    rationale=decision.get("rationale"),
                    duration_ms=tmr.elapsed_ms,
                    evidence={"source": doc.get("source")}
                )
                sys.stdout.write(json.dumps(ev.to_dict(), ensure_ascii=False) + "\n")

    # Also refresh a sidecar index for observability (best-effort local)
    idx = "var/indices/doc_tri_state.jsonl"
    try:
        with open(idx, "a", encoding="utf-8") as fidx:
            fidx.write(json.dumps({"meta": "run_summary", "counts": count}) + "\n")
    except Exception:
        pass

    print(json.dumps({"result": "ok", "counts": count}, ensure_ascii=False))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
