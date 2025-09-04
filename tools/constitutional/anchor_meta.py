from __future__ import annotations
import argparse, json, sys
from pathlib import Path
from typing import Dict, Iterable

FIELDS = ("constitutional_status","constitutional_rule_id","constitutional_rationale")

def load_jsonl(p: Path):
    with p.open("r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)

def write_jsonl(p: Path, rows):
    with p.open("w", encoding="utf-8") as fh:
        for r in rows:
            fh.write(json.dumps(r, ensure_ascii=False) + "\n")

def to_entry(tag: dict) -> dict:
    did = str(tag.get("id") or tag.get("doc_id") or "")
    dec = str(tag.get("decision") or "").upper()
    return {
        "id": did,
        "constitutional_status": dec,
        "constitutional_rule_id": tag.get("rule_id"),
        "constitutional_rationale": tag.get("rationale"),
    }

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Update anchor metadata JSONL with constitutional tri-state")
    ap.add_argument("--tags", required=True, help="JSONL: {id, decision, rule_id?, rationale?}")
    ap.add_argument("--out",  required=True, help="Output JSONL path")
    ap.add_argument("--merge", required=False, help="Existing JSONL to merge (by id)")
    args = ap.parse_args(argv)

    existing: Dict[str, dict] = {}
    if args.merge:
        p = Path(args.merge)
        if p.exists():
            for row in load_jsonl(p):
                did = str(row.get("id") or "")
                if did:
                    existing[did] = row

    updates = {}
    for tag in load_jsonl(Path(args.tags)):
        e = to_entry(tag)
        did = e["id"]
        if not did:
            continue
        base = existing.get(did, {"id": did})
        base.update({k: v for k, v in e.items() if k != "id" and v is not None})
        updates[did] = base

    rows = list(updates.values())
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    write_jsonl(Path(args.out), rows)

    # Simple summary to stdout
    counts = {"ACCEPTABLE":0,"REJECTED":0,"PENDING":0,"UNKNOWN":0}
    for r in rows:
        s = str(r.get("constitutional_status") or "").upper()
        counts[s if s in counts else "UNKNOWN"] += 1
    print(json.dumps({"ok": True, "out": args.out, "counts": counts}, ensure_ascii=False))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
