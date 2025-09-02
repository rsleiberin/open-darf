import argparse
import os
import json
import sys
import collections
from pathlib import Path


def load_text_map(path):
    # expects JSONL with {"doc_id": str, "sent": int, "text": str}
    by_doc = collections.defaultdict(list)
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if not line.strip():
                continue
            obj = json.loads(line)
            by_doc[str(obj.get("doc_id"))].append(
                (int(obj.get("sent", 0)), obj.get("text", ""))
            )
    # sort by sentence index
    for k in by_doc:
        by_doc[k].sort(key=lambda x: x[0])
    return by_doc


def iter_docs(path):
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                yield json.loads(line)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--model",
        required=True,
        help="Path to local HF token-classification checkpoint (no network).",
    )
    ap.add_argument(
        "--input", required=True, help="Normalized BioRED concept split (jsonl)."
    )
    ap.add_argument(
        "--text",
        required=False,
        help="Sentence text mapping JSONL (doc_id, sent, text).",
    )
    ap.add_argument(
        "--out_dir",
        required=True,
        help="Output dir for preds_*.jsonl, metrics_*.json, summary_*.json.",
    )
    ap.add_argument("--split", required=True, choices=["dev", "test", "train"])
    ap.add_argument("--seed", type=int, default=1337)
    args = ap.parse_args()

    # Hermetic checks
    req = ["config.json"]
    weight_ok = any(
        (Path(args.model) / n).exists()
        for n in ("pytorch_model.bin", "model.safetensors")
    )
    if not all((Path(args.model) / n).exists() for n in req) or not weight_ok:
        print(
            "ERR: model directory missing required files (config.json + weights).",
            file=sys.stderr,
        )
        sys.exit(2)

    os.environ["TRANSFORMERS_OFFLINE"] = "1"
    os.environ["HF_HUB_DISABLE_TELEMETRY"] = "1"

    # Lazy import to allow environments w/o deps to still package this tool
    try:
        import torch
        from transformers import (
            AutoTokenizer,
            AutoModelForTokenClassification,
            pipeline,
        )
    except Exception as e:
        print(
            "ERR: transformers/torch not available in this environment:",
            e,
            file=sys.stderr,
        )
        sys.exit(3)

    tok = AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    mdl = AutoModelForTokenClassification.from_pretrained(
        args.model, local_files_only=True
    )
    device = 0 if torch.cuda.is_available() else -1
    nlp = pipeline(
        "token-classification",
        model=mdl,
        tokenizer=tok,
        aggregation_strategy="simple",
        device=device,
    )

    text_map = (
        load_text_map(args.text) if args.text and Path(args.text).exists() else {}
    )

    os.makedirs(args.out_dir, exist_ok=True)
    preds_path = os.path.join(args.out_dir, f"preds_{args.split}.jsonl")
    summ_path = os.path.join(args.out_dir, f"summary_{args.split}.json")
    met_path = os.path.join(args.out_dir, f"metrics_{args.split}.json")

    total_docs = 0
    total_spans = 0
    label_counts = collections.Counter()

    with open(preds_path, "w", encoding="utf-8") as fout:
        for doc in iter_docs(args.input):
            total_docs += 1
            doc_id = str(doc.get("doc_id", f"doc{total_docs}"))
            entities = []
            # run over sentences if text is available
            for sent_idx, sent_text in text_map.get(doc_id, []):
                if not sent_text:
                    continue
                outputs = nlp(sent_text)
                for o in outputs:
                    ent = {
                        "sent": int(sent_idx),
                        "label": o.get("entity_group"),
                        "start": int(o.get("start", 0)),
                        "end": int(o.get("end", 0)),
                        "score": float(o.get("score", 0.0)),
                    }
                    entities.append(ent)
                    label_counts[ent["label"]] += 1
            total_spans += len(entities)
            fout.write(
                json.dumps({"doc_id": doc_id, "entities": entities}, ensure_ascii=False)
                + "\n"
            )

    # Summaries (pred-only; evaluation against gold spans is TBD)
    with open(summ_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "docs": total_docs,
                "pred_spans": total_spans,
                "labels": sorted(list(label_counts)),
            },
            f,
            indent=2,
        )
    with open(met_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "label_counts": dict(label_counts),
                "notes": "Pred-only; gold span eval to be added when spans are available.",
            },
            f,
            indent=2,
        )

    print("✓ Wrote:", preds_path)
    print("✓ Wrote:", summ_path)
    print("✓ Wrote:", met_path)


if __name__ == "__main__":
    main()
