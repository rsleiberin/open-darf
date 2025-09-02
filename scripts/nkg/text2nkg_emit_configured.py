import json
import argparse


def load_jsonl(path):
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                yield json.loads(line)


def mk_edges(doc, mapping, cfg):
    window = int(cfg.get("sentence_window", 1))
    min_cnt = int(cfg.get("min_mapping_count", 1))
    disallowed = set(cfg.get("disallowed_type_pairs", []))
    ents = doc.get("entities", [])
    et = {
        e["id"]: (e.get("type", ""), int(e.get("sent", 0))) for e in ents if "id" in e
    }
    ids = [e["id"] for e in ents if "id" in e]
    edges = []
    for i in range(len(ids)):
        for j in range(i + 1, len(ids)):
            a, b = ids[i], ids[j]
            ta, sa = et.get(a, ("", 0))
            tb, sb = et.get(b, ("", 0))
            if not ta or not tb:
                continue
            if abs(sa - sb) > window:
                continue
            pair_key = "|".join(sorted([ta, tb]))
            if pair_key in disallowed:
                continue
            mm = mapping.get(pair_key)
            if not mm:
                continue
            if int(mm.get("count", 0)) < min_cnt:
                continue
            lab = mm.get("label")
            if not lab:
                continue
            edges.append({"head": a, "tail": b, "type": lab})
    return edges


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--normalized", required=True, help="Normalized BioRED concept split (jsonl)"
    )
    ap.add_argument("--mapping", required=True, help="var/datasets/heuristic_map.json")
    ap.add_argument("--config", required=True, help="var/datasets/re_config.json")
    ap.add_argument(
        "--out", required=True, help="Output JSON with concept_nodes + predicted_edges"
    )
    args = ap.parse_args()

    mapping = json.load(open(args.mapping, "r", encoding="utf-8"))
    cfg = json.load(open(args.config, "r", encoding="utf-8"))
    docs = list(load_jsonl(args.normalized))
    total = len(docs)

    concept_nodes = []
    predicted_edges = []
    for i, d in enumerate(docs, 1):
        doc_id = str(d.get("doc_id", i))
        for e in d.get("entities", []):
            concept_nodes.append(
                {
                    "id": e.get("id"),
                    "doc_id": doc_id,
                    "type": e.get("type", ""),
                    "sent": int(e.get("sent", 0)),
                }
            )
        predicted_edges.extend(
            {"doc_id": doc_id, **edge} for edge in mk_edges(d, mapping, cfg)
        )
        pct = int(i * 100 / total)
        if pct in (25, 50, 75, 100):
            print(f"[{pct}%] processed {i}/{total}")

    out = {
        "concept_nodes": concept_nodes,
        "predicted_edges": predicted_edges,
        "meta": {"config": cfg, "mapping_keys": len(mapping)},
    }
    with open(args.out, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
    print(
        f"✓ Wrote {args.out}   nodes={len(concept_nodes)} edges={len(predicted_edges)}"
    )


if __name__ == "__main__":
    main()
