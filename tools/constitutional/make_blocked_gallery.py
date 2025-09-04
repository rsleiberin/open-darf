from __future__ import annotations
import argparse, json, re
from pathlib import Path
from typing import Dict, Iterable, Tuple

EMAIL_RE = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")
URL_RE   = re.compile(r"https?://\S+")
DIGIT_RE = re.compile(r"\d{4,}")

def load_jsonl(p: Path) -> Iterable[dict]:
    with p.open("r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)

def redacted(text: str, limit: int = 240) -> str:
    t = EMAIL_RE.sub("[email]", text)
    t = URL_RE.sub("[url]", t)
    t = DIGIT_RE.sub("[digits]", t)
    t = t.replace("\n", " ").strip()
    return (t[:limit] + "…") if len(t) > limit else t

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Create blocked-example gallery (markdown)")
    ap.add_argument("--docs", required=True, help="Path to docs.jsonl (must include id,text)")
    ap.add_argument("--tags", required=True, help="Path to tags.jsonl (id,decision)")
    ap.add_argument("--out", required=True, help="Output markdown path")
    args = ap.parse_args(argv)

    docs_path = Path(args.docs); tags_path = Path(args.tags); out = Path(args.out)
    assert docs_path.exists() and tags_path.exists(), "Input files must exist"

    tags: Dict[str,str] = {}
    for t in load_jsonl(tags_path):
        did = str(t.get("id") or t.get("doc_id") or "")
        dec = str(t.get("decision") or "").upper()
        if did:
            tags[did] = dec

    blocked = []
    accepted = []
    pending  = []
    unknown  = []

    for d in load_jsonl(docs_path):
        did = str(d.get("id") or d.get("doc_id") or "")
        txt = d.get("text") or ""
        dec = tags.get(did, "PENDING").upper()
        entry = (did, redacted(str(txt)))
        if dec == "REJECTED":
            blocked.append(entry)
        elif dec == "ACCEPTABLE":
            accepted.append(entry)
        elif dec == "PENDING":
            pending.append(entry)
        else:
            unknown.append(entry)

    md = []
    md.append("# Phase 7C — Blocked Example Gallery\n")
    md.append("This gallery shows **REJECTED** documents with lightly redacted snippets.\n")
    md.append("## Summary\n")
    md.append(f"- ACCEPTABLE: {len(accepted)}\n- REJECTED: {len(blocked)}\n- PENDING: {len(pending)}\n- UNKNOWN: {len(unknown)}\n")
    md.append("\n## Blocked (REJECTED)\n")
    if blocked:
        for did, snip in blocked:
            md.append(f"- **{did}** — {snip}\n")
    else:
        md.append("_(none)_\n")
    md.append("\n## Accepted (ACCEPTABLE)\n")
    if accepted:
        for did, snip in accepted:
            md.append(f"- {did} — {snip}\n")
    else:
        md.append("_(none)_\n")
    md.append("\n## Pending (treated as blocked)\n")
    if pending:
        for did, snip in pending:
            md.append(f"- {did} — {snip}\n")
    else:
        md.append("_(none)_\n")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("".join(md), encoding="utf-8")
    print(json.dumps({"ok": True, "out": str(out)}))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
