# SPDX-License-Identifier: MIT
from __future__ import annotations

from abc import ABC, abstractmethod
from typing import List


class FusionClassifier(ABC):
    """Combines content/context features into bias probabilities."""

    @abstractmethod
    def predict_proba(
        self, content_vec: List[float], context_vec: List[float]
    ) -> List[float]:
        """
        Returns probability for each bias category in a fixed, agreed order.
        """


# ------------------------------
# Tiny deterministic fusion (for tests / CI)
# ------------------------------


def _softmax(xs: List[float]) -> List[float]:
    # numerically stable softmax
    m = max(xs) if xs else 0.0
    exps = [pow(2.718281828, x - m) for x in xs]
    s = sum(exps) or 1.0
    return [e / s for e in exps]


class TinyFusion(FusionClassifier):
    """
    Linear mixer + softmax:
      - Weights chosen to be simple and stable in tests.
      - Expects content_vec: [hedge, assertive, subjective]
      - Expects context_vec: [citation_density, has_methods, gendered]
    Bias order (5): [citation, gender, methodology, representation, outcome]
    """

    def __init__(self, w_content=None, w_context=None, bias_order=5):
        self.wc = w_content or [0.6, 0.8, 0.4]
        self.wx = w_context or [1.0, 0.7, 0.9]
        self.n = bias_order

    def predict_proba(
        self, content_vec: List[float], context_vec: List[float]
    ) -> List[float]:
        # simple hand-crafted signals to keep tests deterministic
        citation_bias = (1.5 - min(1.5, context_vec[0])) + 0.2 * content_vec[1]
        gender_bias = 0.5 * context_vec[2] + 0.1 * content_vec[2]
        methodology_bias = (1.0 - context_vec[1]) + 0.3 * content_vec[0]
        representation_bias = 0.4 * content_vec[2] + 0.2 * content_vec[0]
        outcome_bias = 0.3 * content_vec[1] + 0.2 * content_vec[2]

        raw = [
            citation_bias,
            gender_bias,
            methodology_bias,
            representation_bias,
            outcome_bias,
        ]
        return _softmax(raw)
