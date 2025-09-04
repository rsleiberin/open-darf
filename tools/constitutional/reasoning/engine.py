from __future__ import annotations
from typing import Iterable, Tuple
from time import perf_counter_ns
from .context import ReasoningInput, Explanation, ExplanationMeta

class ExplanationEngine:
    """
    Deterministic, fast-path explanation generator with negligible overhead.
    - Normalizes principle/rationale tokens.
    - Produces a compact Explanation suitable for audit logging.
    """
    __slots__ = ("_normalize_cache",)

    def __init__(self) -> None:
        self._normalize_cache = {}

    @staticmethod
    def _norm_token(t: str) -> str:
        return " ".join(t.strip().split()).lower()

    def _norm_seq(self, xs: Iterable[str]) -> Tuple[str, ...]:
        return tuple(self._norm_token(x) for x in xs)

    def explain(self, rin: ReasoningInput, precedents: Iterable[str] = ()) -> Explanation:
        _ = perf_counter_ns()  # easy probe for perf tests
        principles = self._norm_seq(rin.principles)
        path = self._norm_seq([rin.rationale])
        cited = tuple(precedents)
        conf = min(1.0, 0.6 + 0.05 * len(principles))  # simple heuristic
        meta = ExplanationMeta(confidence=conf, uncertainty_note="")
        return Explanation(
            decision=rin.decision,
            applied_principles=principles,
            reasoning_path=path,
            cited_precedents=cited,
            meta=meta,
        )
