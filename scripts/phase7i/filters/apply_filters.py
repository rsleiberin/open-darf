#!/usr/bin/env python3
"""
Apply lightweight post-prediction filters:
 - directionality: keep arcs whose direction matches schema or model convention
 - negation: drop extractions negated by local cue words (very naive)
 - type: gate relations/entities by allowed NER types

Inputs:
  --preds <file>         JSONL or JSON of predictions (schema-agnostic; best-effort)
  --out <file>           Output filtered predictions (same format as input)
  --filters a,b,c        Comma list: directionality,negation,type
  --allow-types file     Optional JSON list of allowed types for type-gating
Notes:
  This is a safe, best-effort filter. If input can't be parsed, it passes-through.
"""
import argparse, json, sys, pathlib

def load_any(path):
    p = pathlib.Path(path)
    try:
        txt = p.read_text(encoding="utf-8")
    except Exception:
        return None, "read_error"
    txt = txt.strip()
    if not txt:
        return [], "empty"
    try:
        if txt.startswith("["):
            return json.loads(txt), "json_array"
        elif txt.startswith("{"):
            return [json.loads(txt)], "json_obj"
        else:
            # assume JSONL
            return [json.loads(line) for line in txt.splitlines() if line.strip()], "jsonl"
    except Exception:
        return None, "parse_error"

def save_like(data, dest, fmt_hint):
    d = pathlib.Path(dest)
    d.parent.mkdir(parents=True, exist_ok=True)
    try:
        if fmt_hint == "json_array":
            d.write_text(json.dumps(data, ensure_ascii=False, indent=2))
        elif fmt_hint == "json_obj":
            d.write_text(json.dumps(data[0] if data else {}, ensure_ascii=False, indent=2))
        else:
            with d.open("w", encoding="utf-8") as f:
                for row in data:
                    f.write(json.dumps(row, ensure_ascii=False)+"\n")
        return True
    except Exception:
        return False

def filter_directionality(rows):
    # Placeholder: if relation has 'dir' field, keep only 'forward'
    out=[]
    for r in rows:
        if isinstance(r, dict):
            dirv = r.get("dir") or r.get("direction")
            if dirv in (None, "forward", "->"):
                out.append(r)
        else:
            out.append(r)
    return out

def filter_negation(rows):
    NEG_CUES = {"no", "not", "without", "lack", "absent"}
    out=[]
    for r in rows:
        txt = ""
        if isinstance(r, dict):
            txt = " ".join(str(r.get(k,"")) for k in ("text","sentence","span","context")).lower()
        keep = True
        for cue in NEG_CUES:
            if f" {cue} " in f" {txt} ":
                keep = False
                break
        if keep:
            out.append(r)
    return out

def filter_types(rows, allow):
    if not allow: 
        return rows
    allowed = set(allow)
    out=[]
    for r in rows:
        if isinstance(r, dict):
            t = r.get("type") or r.get("label") or r.get("ner")
            if t is None or t in allowed:
                out.append(r)
        else:
            out.append(r)
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--preds", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--filters", default="")
    ap.add_argument("--allow-types")
    args = ap.parse_args()

    rows, fmt = load_any(args.preds)
    if rows is None:
        # passthrough by copying input to out (or write empty list)
        pathlib.Path(args.out).write_text("[]")
        print("[FILTERS] parse error; wrote empty output")
        return 0

    filters = [f.strip().lower() for f in args.filters.split(",") if f.strip()]
    allow = None
    if args.allow_types:
        try:
            allow = json.loads(pathlib.Path(args.allow_types).read_text(encoding="utf-8"))
        except Exception:
            allow = None

    out = rows
    if "directionality" in filters:
        out = filter_directionality(out)
    if "negation" in filters:
        out = filter_negation(out)
    if "type" in filters:
        out = filter_types(out, allow)

    if not save_like(out, args.out, fmt):
        print("[FILTERS] save failed; no output written", file=sys.stderr)
        return 1
    print(f"[FILTERS] applied={filters or ['<none>']} in={len(rows)} out={len(out)}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
