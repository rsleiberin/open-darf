#!/usr/bin/env python3
import json
import os
import argparse
import collections


def read_jsonl(path):
    with open(path, encoding="utf-8") as f:
        for line in f:
            if line.strip():
                yield json.loads(line)


def norm(s):
    if s is None:
        return None
    if isinstance(s, list):
        s = " ".join(map(str, s))
    s = str(s).strip().lower()
    return " ".join(s.split())


def join_span(tokens, st, en):
    return " ".join(tokens[st : en + 1])


def load_split(root, name):
    return list(read_jsonl(os.path.join(root, f"{name}.jsonl")))


def gold_spans(rec):
    # Expect per-sentence tokens + ner [[[start,end,label],...], ...]
    spans = []
    toks = rec.get("tokens") or rec.get("words") or rec.get("sentences")
    ner = rec.get("ner") or rec.get("entities")
    if isinstance(toks, list) and isinstance(ner, list) and len(toks) == len(ner):
        for si, (sent, anns) in enumerate(zip(toks, ner)):
            if not isinstance(sent, list):
                continue
            for ann in anns or []:
                st, en, lab = int(ann[0]), int(ann[1]), str(ann[2])
                spans.append((si, st, en, lab))
    return spans


def build_term_label_dict(train):
    counts = collections.defaultdict(lambda: collections.Counter())
    for rec in train:
        toks = rec.get("tokens") or rec.get("words") or rec.get("sentences")
        for si, st, en, lab in gold_spans(rec):
            phrase = norm(join_span(toks[si], st, en))
            if phrase:
                counts[phrase][lab] += 1
    # majority label per term
    term2label = {t: cnt.most_common(1)[0][0] for t, cnt in counts.items()}
    return term2label


def predict_spans(rec, term2label, max_len=6):
    preds = []
    toks = rec.get("tokens") or rec.get("words") or rec.get("sentences")
    if not isinstance(toks, list):
        return preds
    for si, sent in enumerate(toks):
        if not isinstance(sent, list):
            continue
        n = len(sent)
        used = [False] * n
        # Greedy longest-match to reduce overlaps
        for L in range(min(max_len, n), 0, -1):
            i = 0
            while i + L <= n:
                if any(used[i : i + L]):
                    i += 1
                    continue
                phrase = norm(" ".join(sent[i : i + L]))
                lab = term2label.get(phrase)
                if lab:
                    preds.append((si, i, i + L - 1, lab))
                    for k in range(i, i + L):
                        used[k] = True
                    i += L
                else:
                    i += 1
    return preds


def eval_entities(gold, pred):
    G = set(gold)
    P = set(pred)
    TP = len(G & P)
    FP = len(P - G)
    FN = len(G - P)
    Pm = TP / (TP + FP) if TP + FP > 0 else 0.0
    Rm = TP / (TP + FN) if TP + FN > 0 else 0.0
    F1 = (2 * Pm * Rm / (Pm + Rm)) if (Pm + Rm) > 0 else 0.0
    return {"tp": TP, "fp": FP, "fn": FN, "P": Pm, "R": Rm, "F1": F1}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="data/scierc_norm")
    ap.add_argument("--split", default="test")
    ap.add_argument("--outdir", required=True)
    args = ap.parse_args()

    os.makedirs(args.outdir, exist_ok=True)
    train = load_split(args.root, "train")
    test = load_split(args.root, args.split)

    term2label = build_term_label_dict(train)

    all_gold = []
    all_pred = []
    for rec in test:
        g = gold_spans(rec)
        p = predict_spans(rec, term2label)
        all_gold.extend(g)
        all_pred.extend(p)

    metrics = eval_entities(all_gold, all_pred)
    summary = {
        "status": "ok",
        "split": args.split,
        "pred_spans": len(all_pred),
        "gold_spans": len(all_gold),
        "precision": metrics["P"],
        "recall": metrics["R"],
        "entity_f1": metrics["F1"],
    }
    # receipts
    open(os.path.join(args.outdir, f"metrics_{args.split}.json"), "w").write(
        json.dumps(
            {"task": "scierc_entities_official", "split": args.split, "micro": metrics},
            indent=2,
        )
    )
    open(os.path.join(args.outdir, f"summary_{args.split}.json"), "w").write(
        json.dumps(summary, indent=2)
    )
    print(
        json.dumps(
            {
                "wrote": [os.path.join(args.outdir, f"metrics_{args.split}.json")],
                **summary,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
