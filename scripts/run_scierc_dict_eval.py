#!/usr/bin/env python3
import json
import os
import argparse
import time
from pathlib import Path


def read_jsonl(path):
    with open(path, encoding="utf-8") as f:
        for line in f:
            if line.strip():
                yield json.loads(line)


def load_split(root, name):
    p = Path(root) / f"{name}.jsonl"
    return list(read_jsonl(p))


def norm(s):
    if s is None:
        return None
    if isinstance(s, list):
        s = " ".join(map(str, s))
    s = str(s).strip().lower()
    return " ".join(s.split())


def gold_strings_scierc(rec):
    # SciERC_norm style: sentences with ner spans and tokens per sentence
    S = set()
    toks = rec.get("tokens") or rec.get("words") or rec.get("sentences")
    ner = rec.get("ner")
    if isinstance(toks, list) and isinstance(ner, list) and len(toks) == len(ner):
        for sent, spans in zip(toks, ner):
            if not isinstance(sent, list):
                continue
            for st, en, _lbl in spans:
                st = int(st)
                en = int(en)
                phrase = " ".join(sent[st : en + 1])
                ns = norm(phrase)
                if ns:
                    S.add(ns)
    # fallback: flattened mentions if present
    for m in rec.get("mentions", []) or []:
        ns = norm(m.get("text"))
        if ns:
            S.add(ns)
    return S


def build_dict(train):
    vocab = set()
    for rec in train:
        vocab |= gold_strings_scierc(rec)
    # keep only terms length>=3 chars
    return {t for t in vocab if len(t) >= 3}


def find_mentions(text, vocab):
    txt = norm(text or "")
    preds = set()
    # naive substring search for each vocab term
    for term in vocab:
        if term in txt:
            preds.add(term)
    return preds


def extract_text_scierc(rec):
    # build doc text by joining tokens
    toks = rec.get("tokens") or rec.get("words") or rec.get("sentences")
    if isinstance(toks, list):
        parts = []
        for sent in toks:
            if isinstance(sent, list):
                parts.append(" ".join(sent))
        return " ".join(parts)
    return rec.get("text") or ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="data/scierc_norm")
    ap.add_argument("--split", default="test")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()

    os.makedirs(args.outdir, exist_ok=True)
    train = load_split(args.root, "train")
    _dev = load_split(args.root, "dev")
    test = load_split(args.root, args.split)

    vocab = build_dict(train)
    # Eval on chosen split
    tp = fp = fn = 0
    docs_scored = 0
    pred_path = os.path.join(args.outdir, f"preds_{args.split}.jsonl")
    t0 = time.time()
    with open(pred_path, "w", encoding="utf-8") as out:
        for i, rec in enumerate(test):
            if args.limit and i >= args.limit:
                break
            gid = str(rec.get("doc_key") or rec.get("id") or i)
            text = extract_text_scierc(rec)
            preds = find_mentions(text, vocab)
            gold = gold_strings_scierc(rec)
            tp += len(preds & gold)
            fp += len(preds - gold)
            fn += len(gold - preds)
            docs_scored += 1
            out.write(
                json.dumps(
                    {"id": gid, "pred_terms": sorted(list(preds))}, ensure_ascii=False
                )
                + "\n"
            )
    t1 = time.time()
    P = tp / (tp + fp) if (tp + fp) > 0 else 0.0
    R = tp / (tp + fn) if (tp + fn) > 0 else 0.0
    F1 = (2 * P * R / (P + R)) if (P + R) > 0 else 0.0
    summary = {
        "status": "ok",
        "split": args.split,
        "docs_scored": docs_scored,
        "precision": P,
        "recall": R,
        "entity_f1": F1,
        "wall_seconds": round(t1 - t0, 4),
    }
    metrics = {
        "task": "scierc_dictmatch",
        "split": args.split,
        "micro": {"tp": tp, "fp": fp, "fn": fn, "P": P, "R": R, "F1": F1},
    }
    open(os.path.join(args.outdir, f"summary_{args.split}.json"), "w").write(
        json.dumps(summary, indent=2)
    )
    open(os.path.join(args.outdir, f"metrics_{args.split}.json"), "w").write(
        json.dumps(metrics, indent=2)
    )
    print(json.dumps({"wrote": [pred_path], **summary}, indent=2))


if __name__ == "__main__":
    main()
