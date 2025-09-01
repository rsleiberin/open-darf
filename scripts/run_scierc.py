#!/usr/bin/env python3
import argparse
import json
import time
import platform
import re
from json import JSONDecodeError, JSONDecoder
from pathlib import Path


def load_json_any(path: Path):
    txt = path.read_text(encoding="utf-8")
    # 1) Try standard JSON
    try:
        return json.loads(txt)
    except JSONDecodeError:
        pass
    # 2) Try JSON Lines (one JSON value per line)
    items = []
    ok = True
    for ln in txt.splitlines():
        s = ln.strip()
        if not s:
            continue
        try:
            items.append(json.loads(s))
        except JSONDecodeError:
            ok = False
            break
    if ok and items:
        return items
    # 3) Try concatenated JSON fragments (no commas between)
    items = []
    dec = JSONDecoder()
    i = 0
    n = len(txt)
    while i < n:
        # skip whitespace
        m = re.search(r"\S", txt[i:])
        if not m:
            break
        i += m.start()
        try:
            obj, j = dec.raw_decode(txt, i)
            items.append(obj)
            i = j
        except JSONDecodeError:
            break
    if items:
        return items
    raise JSONDecodeError("Unsupported JSON format", txt, 0)


def normalize_docs(root):
    # Accept either list of docs or {"data":[...]}
    if isinstance(root, dict) and "data" in root and isinstance(root["data"], list):
        return root["data"]
    if isinstance(root, list):
        return root
    raise ValueError("Unexpected JSON root type")


def count_gold(docs):
    ent = 0
    rel = 0
    for d in docs:
        # DyGIEpp style
        if "ner" in d and isinstance(d["ner"], list):
            for s in d["ner"]:
                try:
                    ent += len(s)
                except Exception:
                    pass
        if "relations" in d and isinstance(d["relations"], list):
            for s in d["relations"]:
                try:
                    rel += len(s)
                except Exception:
                    pass
        # PURE/alt
        if isinstance(d.get("entities"), list):
            ent += len(d["entities"])
        if isinstance(d.get("rels"), list):
            rel += len(d["rels"])
    return ent, rel


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="scibert")
    ap.add_argument("--data", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--seed", type=int, default=42)
    args = ap.parse_args()

    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    splits = {}
    for name in ("train", "dev", "validation", "test"):
        p = Path(args.data) / f"{name}.json"
        if p.exists():
            root = load_json_any(p)
            docs = normalize_docs(root)
            splits[name] = docs
    if "test" not in splits:
        (out_dir / "ERROR_no_test.txt").write_text("missing test.json")
        print("ERROR: missing test.json", flush=True)
        return 2

    gold_ents = {}
    gold_rels = {}
    for s, docs in splits.items():
        e, r = count_gold(docs)
        gold_ents[s] = e
        gold_rels[s] = r

    def metrics(gold):
        tp = 0
        fp = 0
        fn = gold
        prec = 0.0 if (tp + fp) == 0 else tp / (tp + fp)
        rec = 0.0 if (tp + fn) == 0 else tp / (tp + fn)
        f1 = 0.0 if (prec + rec) == 0 else 2 * prec * rec / (prec + rec)
        return {
            "tp": tp,
            "fp": fp,
            "fn": fn,
            "precision": prec,
            "recall": rec,
            "f1": f1,
        }

    metrics_ent = {s: metrics(g) for s, g in gold_ents.items()}
    metrics_rel = {s: metrics(g) for s, g in gold_rels.items()}

    wall = time.time() - t0
    try:
        import torch

        cuda_avail = bool(torch.cuda.is_available())
        gpu_name = torch.cuda.get_device_name(0) if cuda_avail else None
        cuda_ver = getattr(torch.version, "cuda", None)
    except Exception:
        cuda_avail = False
        gpu_name = None
        cuda_ver = None

    (out_dir / "metrics.json").write_text(
        json.dumps(
            {
                "task": "scierc",
                "model": args.model,
                "micro_entity": metrics_ent.get("test", {"f1": 0}),
                "micro_relation": metrics_rel.get("test", {"f1": 0}),
                "gold_counts": {"entities": gold_ents, "relations": gold_rels},
                "timing": {"wall_seconds": wall},
                "env": {
                    "python": platform.python_version(),
                    "torch_cuda_available": cuda_avail,
                    "cuda_version": cuda_ver,
                    "gpu_name": gpu_name,
                },
            },
            indent=2,
        )
    )
    (out_dir / "raw_counts.json").write_text(
        json.dumps({"entities": gold_ents, "relations": gold_rels}, indent=2)
    )
    print(
        json.dumps(
            {
                "status": "ok",
                "wall_seconds": wall,
                "gold_test_entities": gold_ents.get("test", 0),
                "gold_test_relations": gold_rels.get("test", 0),
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
