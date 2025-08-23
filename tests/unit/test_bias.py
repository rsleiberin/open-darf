import json
from pathlib import Path

from apps.document_processor.bias import score_bias, filter_segments

GOLD = []
with open(
    Path(__file__).parent.parent / "golden" / "bias" / "gold.jsonl",
    "r",
    encoding="utf-8",
) as f:
    for line in f:
        GOLD.append(json.loads(line))


def test_score_bias_thresholding_and_reasons_present():
    r = score_bias("This is clearly the best and will always succeed.")
    assert r.label == "flag"
    assert r.score >= 0.5
    assert any(
        "absolutes" in reason or "intensifiers" in reason for reason in r.reasons
    )


def test_filter_segments_counts_and_indices_stable():
    segs = [g["text"] for g in GOLD]
    out = filter_segments(segs, threshold=0.5)
    assert out["kept_count"] + out["removed_count"] == len(segs)
    # sanity: we expect at least one kept and one removed
    assert out["kept_count"] >= 1
    assert out["removed_count"] >= 1
    # indices are stable
    kept_idx = [i for i, _ in out["kept"]]
    removed_idx = [i for i, _, _ in out["removed"]]
    assert set(kept_idx).isdisjoint(set(removed_idx))


def test_gold_f1_is_reasonable_for_toy_set():
    # Compute micro-F1 on the tiny gold
    y_true = [1 if g["label"] == "flag" else 0 for g in GOLD]
    y_pred = [1 if score_bias(g["text"]).label == "flag" else 0 for g in GOLD]
    tp = sum(1 for t, p in zip(y_true, y_pred) if t == 1 and p == 1)
    fp = sum(1 for t, p in zip(y_true, y_pred) if t == 0 and p == 1)
    fn = sum(1 for t, p in zip(y_true, y_pred) if t == 1 and p == 0)
    precision = tp / (tp + fp) if (tp + fp) else 1.0
    recall = tp / (tp + fn) if (tp + fn) else 1.0
    f1 = (
        (2 * precision * recall / (precision + recall)) if (precision + recall) else 1.0
    )
    assert f1 >= 0.8, f"toy gold F1 too low: {f1:.3f}"
