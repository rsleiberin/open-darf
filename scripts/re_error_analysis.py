#!/usr/bin/env python3
import argparse, json, os
from collections import Counter

HEAD_KEYS = {"head","h","subj","subject","arg1","lhs"}
TAIL_KEYS = {"tail","t","obj","object","arg2","rhs"}
TYPE_KEYS = {"type","rel","relation","label","r","predicate"}

def as_int(x):
    try:
        return int(x)
    except Exception:
        return None

def to_exclusive(span):
    if span is None:
        return None
    s, e = span
    return (int(s), int(e) + 1)  # convert end-inclusive → end-exclusive

def get_span(obj):
    if obj is None:
        return None
    if isinstance(obj, (list, tuple)) and len(obj) >= 2 and all(isinstance(v, (int, float)) for v in obj[:2]):
        return (int(obj[0]), int(obj[1]))
    if isinstance(obj, dict):
        if "start" in obj and "end" in obj:
            return (int(obj["start"]), int(obj["end"]))
        if "span" in obj and isinstance(obj["span"], dict) and "start" in obj["span"] and "end" in obj["span"]:
            s = obj["span"]
            return (int(s["start"]), int(s["end"]))
        if "indices" in obj and isinstance(obj["indices"], (list, tuple)) and len(obj["indices"]) >= 2:
            return (int(obj["indices"][0]), int(obj["indices"][1]))
    return None

def iou(a, b):
    if a is None or b is None:
        return 0.0
    s1, e1 = a
    s2, e2 = b
    inter = max(0, min(e1, e2) - max(s1, s2))
    union = max(e1, e2) - min(s1, s2)
    return (inter / union) if union > 0 else 0.0

def nearest_entity_by_span(span, entities):
    if span is None or not entities:
        return None
    s, e = span
    c = (s + e) // 2
    best_i = None
    best_iou = -1.0
    best_dist = 10**9
    for i, ent in enumerate(entities):
        sp = ent.get("span")
        if sp is None:
            continue
        j = iou(span, sp)
        if j > best_iou + 1e-9:
            best_i = i
            best_iou = j
            best_dist = abs(c - ((sp[0] + sp[1]) // 2))
        elif abs(j - best_iou) < 1e-9:
            d = abs(c - ((sp[0] + sp[1]) // 2))
            if d < best_dist:
                best_i = i
                best_dist = d
    return best_i

def norm_entity(e):
    # Accept dict or triple [s,e,label]; convert to end-exclusive
    if isinstance(e, dict):
        sp = to_exclusive(get_span(e))
        lab = e.get("type") or e.get("label") or e.get("entity_type") or "UNK"
        return {"span": sp, "type": lab, "text": e.get("text")}
    if isinstance(e, (list, tuple)) and len(e) >= 3 and all(isinstance(v, (int, float)) for v in e[:2]):
        sp = to_exclusive((int(e[0]), int(e[1])))
        return {"span": sp, "type": str(e[2]), "text": None}
    return {"span": None, "type": "UNK", "text": None}

def flatten_ner(ner):
    out = []
    def rec(x):
        if isinstance(x, (list, tuple)):
            if len(x) >= 3 and all(isinstance(v, (int, float)) for v in x[:2]):
                out.append(norm_entity(x))
            else:
                for y in x:
                    rec(y)
        elif isinstance(x, dict):
            out.append(norm_entity(x))
    rec(ner)
    # de-dup by span
    seen = set()
    uniq = []
    for e in out:
        if e["span"] is None:
            continue
        if e["span"] in seen:
            continue
        seen.add(e["span"])
        uniq.append(e)
    return uniq

def extract_entities(rec):
    for key in ("entities", "entity_mentions", "spans", "ner", "mentions"):
        v = rec.get(key)
        if isinstance(v, (list, tuple)):
            return flatten_ner(v)
    return []

def flatten_rels(rels):
    out = []
    def rec(x):
        if isinstance(x, (list, tuple)):
            # A single relation item: [h_s,h_e,t_s,t_e,'REL'] (label last)
            if len(x) >= 5 and isinstance(x[-1], str) and all(isinstance(v, (int, float)) for v in x[:4]):
                out.append(x)
            else:
                for y in x:
                    rec(y)
        elif isinstance(x, dict):
            out.append(x)
    rec(rels)
    return out

def get_rels(rec):
    for k in ("relations", "relation_mentions", "rels", "triples"):
        v = rec.get(k)
        if isinstance(v, (list, tuple)):
            return flatten_rels(v)
    return []

def shape_tag(obj):
    if isinstance(obj, dict):
        return "DICT"
    if isinstance(obj, (list, tuple)):
        kinds = []
        for x in obj[:min(6, len(obj))]:
            if isinstance(x, (int, float)):
                kinds.append("NUM")
            elif isinstance(x, str):
                kinds.append("STR")
            elif isinstance(x, (list, tuple, dict)):
                kinds.append("OBJ")
            else:
                kinds.append(type(x).__name__.upper())
        return f"LIST[n={len(obj)};{'+'.join(kinds)}]"
    return type(obj).__name__.upper()

def norm_relation(r, entities):
    shp = shape_tag(r)
    rtype = "UNK"
    head_idx = tail_idx = None
    head_span = tail_span = None

    if isinstance(r, dict):
        hv = next((r[k] for k in HEAD_KEYS if k in r), None)
        tv = next((r[k] for k in TAIL_KEYS if k in r), None)
        rv = next((r[k] for k in TYPE_KEYS if k in r), None)
        rtype = str(rv) if rv is not None else "UNK"
        # head
        hi = as_int(hv)
        if hi is not None and 0 <= hi < len(entities):
            head_idx = hi; head_span = entities[hi]["span"]
        else:
            hs = to_exclusive(get_span(hv)) if not isinstance(hv, int) else None
            if hs is not None:
                idx = nearest_entity_by_span(hs, entities)
                if idx is not None:
                    head_idx = idx; head_span = entities[idx]["span"]
        # tail
        ti = as_int(tv)
        if ti is not None and 0 <= ti < len(entities):
            tail_idx = ti; tail_span = entities[ti]["span"]
        else:
            ts = to_exclusive(get_span(tv)) if not isinstance(tv, int) else None
            if ts is not None:
                idx = nearest_entity_by_span(ts, entities)
                if idx is not None:
                    tail_idx = idx; tail_span = entities[idx]["span"]

    elif isinstance(r, (list, tuple)):
        # Interpret as [h_s,h_e,t_s,t_e,'REL']
        label = None
        for x in reversed(r):
            if isinstance(x, str):
                label = x
                break
        if label is not None:
            rtype = str(label)
        nums = [int(x) for x in r if isinstance(x, (int, float))]
        if len(nums) >= 4:
            head_span = to_exclusive((nums[0], nums[1]))
            tail_span = to_exclusive((nums[2], nums[3]))
            hi = nearest_entity_by_span(head_span, entities)
            ti = nearest_entity_by_span(tail_span, entities)
            if hi is not None:
                head_idx = hi
            if ti is not None:
                tail_idx = ti

    return {
        "type": rtype,
        "head_idx": head_idx, "tail_idx": tail_idx,
        "head_span": head_span, "tail_span": tail_span,
        "shape": shp
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp", required=True)
    ap.add_argument("--out", dest="out", required=True)
    ap.add_argument("--notes", dest="notes", required=True)
    ap.add_argument("--shapes", dest="shapes", required=True)
    args = ap.parse_args()

    total = resolved = unresolved = 0
    shape_counts = Counter(); typepair = Counter()
    shape_examples = {}

    with open(args.inp, "r", encoding="utf-8") as f, open(args.out, "w", encoding="utf-8") as fo:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except Exception:
                continue
            ents = extract_entities(rec)
            rels = get_rels(rec)
            for r in rels:
                total += 1
                nr = norm_relation(r, ents)
                shape_counts[nr["shape"]] += 1
                if nr["head_idx"] is not None and nr["tail_idx"] is not None:
                    resolved += 1
                    ht = ents[nr["head_idx"]]["type"] if nr["head_idx"] < len(ents) else "UNK"
                    tt = ents[nr["tail_idx"]]["type"] if nr["tail_idx"] < len(ents) else "UNK"
                    typepair[(nr["type"], ht, tt)] += 1
                else:
                    unresolved += 1
                if nr["shape"] not in shape_examples:
                    shape_examples[nr["shape"]] = {"raw": r, "normalized": nr}
                fo.write(json.dumps(nr) + "\n")

    with open(args.shapes, "w", encoding="utf-8") as fs:
        json.dump({"shape_counts": dict(shape_counts), "examples": shape_examples}, fs, indent=2)

    with open(args.notes, "w", encoding="utf-8") as fn:
        fn.write("# SciERC Relation Shapes & Parser Notes\n\n")
        fn.write(f"- Total relation items: **{total}**\n")
        fn.write(f"- Resolved to (head,tail): **{resolved}**\n")
        fn.write(f"- Unresolved: **{unresolved}**\n\n")
        fn.write("## Top Shapes\n")
        for shp, count in sorted(shape_counts.items(), key=lambda x: (-x[1], x[0]))[:10]:
            fn.write(f"- `{shp}` → {count}\n")
        fn.write("\n## Top Relation Type × (HeadEnt, TailEnt)\n")
        for (rtype, h, t), c in sorted(typepair.items(), key=lambda x: -x[1])[:20]:
            fn.write(f"- `{rtype}` : {h} → {t} — {c}\n")

if __name__ == "__main__":
    main()
