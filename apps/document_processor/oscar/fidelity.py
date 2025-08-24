# SPDX-License-Identifier: MIT
from __future__ import annotations
from abc import ABC, abstractmethod
from typing import List
import difflib
import re


class SemanticFidelityValidator(ABC):
    @abstractmethod
    def compare_semantic_preservation(self, original: str, modified: str) -> float: ...


class TinySemanticFidelityValidator(SemanticFidelityValidator):
    """
    Token Jaccard + token-sequence similarity with equivalence normalization.
    If lexical content (raw tokens) changes, apply a small cap so ultra-high thresholds
    (e.g., 0.999) require exact lexical preservation.
    """

    _token_re = re.compile(r"[A-Za-z0-9]+")
    _equiv = {
        "men": "participants",
        "women": "participants",
        "male": "participants",
        "female": "participants",
        "man": "participants",
        "woman": "participants",
        "he": "they",
        "she": "they",
        "participants": "participants",
        "subjects": "participants",
    }

    def _raw_tokens(self, s: str) -> List[str]:
        return [t.lower() for t in self._token_re.findall(s)]

    def _norm_tokens(self, s: str) -> List[str]:
        toks = self._raw_tokens(s)
        return [self._equiv.get(t, t) for t in toks]

    def compare_semantic_preservation(self, original: str, modified: str) -> float:
        toks_o = self._norm_tokens(original)
        toks_m = self._norm_tokens(modified)
        set_o, set_m = set(toks_o), set(toks_m)
        if not set_o:
            return 1.0 if not set_m else 0.0

        # Base score with normalized tokens
        jacc = len(set_o & set_m) / max(1, len(set_o | set_m))
        seq = difflib.SequenceMatcher(a=toks_o, b=toks_m).ratio()
        score = 0.6 * jacc + 0.4 * seq

        # Penalize lexical changes (even if normalized equivalents) to avoid perfect 1.0
        if self._raw_tokens(original) != self._raw_tokens(modified):
            score = min(score, 0.995)

        return float(score)
