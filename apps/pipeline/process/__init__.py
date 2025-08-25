from __future__ import annotations
from typing import Dict, Any


# Minimal, deterministic bias-check stub used by the runner.
# Keeps PR CI service-free and fast.
def run_bias_checks(text: str) -> Dict[str, Any]:
    text_l = (text or "").lower()
    cues = {
        "loaded_language": ["clearly", "undeniable", "obviously"],
        "hedging": ["might", "could", "perhaps", "suggests"],
        "appeal_to_authority": ["experts say", "studies show"],
    }
    counts = {k: 0 for k in cues}
    hits = []
    for label, words in cues.items():
        for w in words:
            if w in text_l:
                counts[label] += 1
                hits.append((label, w))
    # derive a tiny deterministic 'cbdt' score compatible with sanity test expectations
    labels_hit = sorted([k for k, v in counts.items() if v])
    score = min(1.0, len(labels_hit) / 3.0)
    return {
        "counts": {k: v for k, v in counts.items() if v},
        "hits": hits[:5],
        "cbdt": {"score": score, "labels": labels_hit},
    }


__all__ = ["run_bias_checks"]
