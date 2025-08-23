from __future__ import annotations
from dataclasses import dataclass
from typing import List, Tuple, Dict

# Simple, transparent heuristics — deterministic & testable.
# We avoid sensitive lists; this focuses on overclaim / absolutist language.
_ABSOLUTES = {
    "always",
    "never",
    "everyone",
    "no one",
    "nobody",
    "all",
    "none",
    "obviously",
    "clearly",
    "undeniably",
    "best",
    "worst",
    "perfect",
    "guaranteed",
}
_INTENSIFIERS = {"extremely", "highly", "incredibly", "totally", "completely"}


@dataclass(frozen=True)
class BiasResult:
    label: str  # "ok" | "flag"
    score: float  # 0..1 (higher = more biased by our heuristic)
    reasons: Tuple[str, ...]


def _score_text(text: str) -> Tuple[float, List[str]]:
    t = text.lower()
    reasons: List[str] = []
    hits_abs = [w for w in _ABSOLUTES if w in t]
    hits_int = [w for w in _INTENSIFIERS if w in t]
    score = 0.0
    if hits_abs:
        score += min(0.7, 0.1 * len(hits_abs) + 0.4)  # absolutes weigh heavily
        reasons.append(f"absolutes:{len(hits_abs)}")
    if hits_int:
        score += min(0.3, 0.05 * len(hits_int) + 0.05)
        reasons.append(f"intensifiers:{len(hits_int)}")
    return (min(score, 1.0), reasons)


def score_bias(text: str, *, threshold: float = 0.5) -> BiasResult:
    score, reasons = _score_text(text)
    label = "flag" if score >= threshold else "ok"
    return BiasResult(label=label, score=score, reasons=tuple(reasons))


def filter_segments(
    segments: List[str], *, threshold: float = 0.5
) -> Dict[str, object]:
    kept: List[Tuple[int, str]] = []
    removed: List[Tuple[int, str, float]] = []
    for i, s in enumerate(segments):
        r = score_bias(s, threshold=threshold)
        if r.label == "flag":
            removed.append((i, s, r.score))
        else:
            kept.append((i, s))
    return {
        "kept": kept,
        "removed": removed,
        "kept_count": len(kept),
        "removed_count": len(removed),
        "threshold": threshold,
    }
