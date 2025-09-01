#!/usr/bin/env python3
import argparse
import json
import platform
import time
from pathlib import Path


def iter_jsonl(p: Path):
    for ln in p.read_text(encoding="utf-8").splitlines():
        ln = ln.strip()
        if not ln:
            continue
        yield json.loads(ln)


def count_gold_jsonl(p: Path):
    ents = 0
    rels = 0
    for obj in iter_jsonl(p):
        if isinstance(obj.get("entities"), list):
            ents += len(obj["entities"])
        if isinstance(obj.get("relations"), list):
            rels += len(obj["relations"])
    return ents, rels


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="biobert")
    ap.add_argument("--data", required=True)  # directory with *.jsonl
    ap.add_argument("--out", required=True)
    ap.add_argument("--seed", type=int, default=42)
    args = ap.parse_args()

    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    gold_ents = {}
    gold_rels = {}
    for split in ("train", "dev", "validation", "test"):
        p = Path(args.data) / f"{split}.jsonl"
        if p.exists():
            e, r = count_gold_jsonl(p)
            gold_ents[split] = e
            gold_rels[split] = r
    if "test" not in gold_ents:
        (out / "ERROR_no_test.txt").write_text("missing test.jsonl")
        return 2

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

    m_ent = metrics(gold_ents["test"])
    m_rel = metrics(gold_rels["test"])
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

    (out / "metrics.json").write_text(
        json.dumps(
            {
                "task": "biored",
                "model": args.model,
                "micro_entity": m_ent,
                "micro_relation": m_rel,
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
