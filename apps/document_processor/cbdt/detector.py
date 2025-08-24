# SPDX-License-Identifier: MIT
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Dict, Iterable, List, Mapping, Optional

from .models import ContentModel, ContextModel, TinyContentModel, TinyContextModel
from .fusion import FusionClassifier, TinyFusion


class BiasCategory(str, Enum):
    CITATION = "citation_bias"
    GENDER = "gender_bias"
    METHODOLOGY = "methodology_bias"
    REPRESENTATION = "representation_bias"
    OUTCOME = "outcome_bias"


DEFAULT_ORDER: List[BiasCategory] = [
    BiasCategory.CITATION,
    BiasCategory.GENDER,
    BiasCategory.METHODOLOGY,
    BiasCategory.REPRESENTATION,
    BiasCategory.OUTCOME,
]


@dataclass
class CBDTConfig:
    threshold: float = 0.5  # default per-class prob threshold for flagging
    categories: List[BiasCategory] = None

    def __post_init__(self):
        if self.categories is None:
            self.categories = list(DEFAULT_ORDER)


class CBDTBiasDetector:
    """
    Orchestrates dual-encoder + fusion to detect bias categories.

    DI points (all optional):
      - content_model: ContentModel
      - context_model: ContextModel
      - fusion: FusionClassifier
      - config: CBDTConfig
    """

    def __init__(
        self,
        content_model: Optional[ContentModel] = None,
        context_model: Optional[ContextModel] = None,
        fusion: Optional[FusionClassifier] = None,
        config: Optional[CBDTConfig] = None,
    ):
        self.content_model = content_model or TinyContentModel()
        self.context_model = context_model or TinyContextModel()
        self.fusion = fusion or TinyFusion()
        self.config = config or CBDTConfig()

    def predict(
        self,
        text: str,
        citations: Optional[Iterable[str]] = None,
        metadata: Optional[Mapping] = None,
    ) -> Dict[str, float]:
        """Returns dict: category -> probability."""
        c_vec = self.content_model.encode(text)
        x_vec = self.context_model.encode(text, citations=citations, metadata=metadata)
        probs = self.fusion.predict_proba(c_vec, x_vec)
        return {cat.value: float(p) for cat, p in zip(self.config.categories, probs)}

    def classify(
        self,
        text: str,
        citations: Optional[Iterable[str]] = None,
        metadata: Optional[Mapping] = None,
    ) -> Dict[str, Dict[str, float]]:
        """
        Returns:
          {
            "scores": {category: prob, ...},
            "flags": {category: 0/1, ...}
          }
        """
        scores = self.predict(text, citations, metadata)
        flags = {
            k: 1.0 if v >= self.config.threshold else 0.0 for k, v in scores.items()
        }
        return {"scores": scores, "flags": flags}
