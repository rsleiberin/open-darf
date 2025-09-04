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

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Gate span outputs by TriState tags (fail-closed)")
    ap.add_argument("--spans-in", required=True, help="JSONL spans; each row must include doc_id")
    ap.add_argument("--tags", required=True)
    ap.add_argument("--spans-out", required=True)
    ap.add_argument("--audit-stdout", action="store_true")
    args = ap.parse_args(argv)

    decisions = tag_map(args.tags)
    kept = dropped = 0

    with open(args.spans_out, "w", encoding="utf-8") as so:
        for s in load_jsonl(args.spans_in):
            did = str(s.get("doc_id") or s.get("id") or "")
            dec = decisions.get(did, "PENDING").upper()
            if dec in ALLOWED:
                kept += 1
                so.write(json.dumps(s, ensure_ascii=False) + "\n")
                if args.audit_stdout:
                    sys.stdout.write(json.dumps({"stage":"extract","object":"span","doc_id":did,"decision":"ACCEPTABLE"})+"\n")
            else:
                dropped += 1
                if args.audit_stdout:
                    sys.stdout.write(json.dumps({"stage":"extract","object":"span","doc_id":did,"decision":"REJECTED"})+"\n")

    print(json.dumps({"spans_kept": kept, "spans_dropped": dropped}, ensure_ascii=False))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
