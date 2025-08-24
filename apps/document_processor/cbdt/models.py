# SPDX-License-Identifier: MIT
from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Iterable, List, Mapping, Optional


class ContentModel(ABC):
    """Encodes the document text into a numeric feature vector."""

    @abstractmethod
    def encode(self, text: str) -> List[float]:
        """Return a fixed-length feature vector for the given text."""


class ContextModel(ABC):
    """Encodes context (citations, methods, authorship hints) into features."""

    @abstractmethod
    def encode(
        self,
        text: str,
        citations: Optional[Iterable[str]] = None,
        metadata: Optional[Mapping] = None,
    ) -> List[float]:
        """Return a fixed-length feature vector for the given context."""


# ------------------------------
# Tiny deterministic reference models (for tests / CI)
# ------------------------------


class TinyContentModel(ContentModel):
    """
    Counts a few heuristic tokens that often correlate with biased phrasing.
    Output: [hedge_count, assertive_count, subjective_count]
    """

    HEDGES = {"we believe", "it seems", "likely", "appears"}
    ASSERTIVE = {"clearly", "obviously", "undeniably"}
    SUBJECTIVE = {"best", "worst", "groundbreaking", "revolutionary"}

    def encode(self, text: str) -> List[float]:
        t = text.lower()
        hedge = sum(t.count(k) for k in self.HEDGES)
        assertive = sum(t.count(k) for k in self.ASSERTIVE)
        subjective = sum(t.count(k) for k in self.SUBJECTIVE)
        return [float(hedge), float(assertive), float(subjective)]


class TinyContextModel(ContextModel):
    """
    Encodes simple context cues:
    - citation_density: citations per 1k chars (simulated by count of '[' or 'doi')
    - method_markers: presence of words that indicate methods section exists
      (with a negation override for phrases like "no methodology")
    - gendered_terms: naive count of gendered tokens in surrounding content
    Output: [citation_density, has_methods, gendered_score]
    """

    METHOD_MARKERS = {"methods", "methodology", "we conducted", "we measured"}
    NEGATION_MARKERS = {
        "no methodology",
        "no methods",
        "without methodology",
        "without methods",
        "no method",
        "lack of methodology",
        "lack of methods",
        "absent methods",
        "insufficient methods",
    }
    GENDERED = {"he", "she", "male", "female", "men", "women"}

    def encode(
        self,
        text: str,
        citations: Optional[Iterable[str]] = None,
        metadata: Optional[Mapping] = None,
    ) -> List[float]:
        t = text.lower()

        # crude citation signal
        c_hits = (
            t.count("[") + t.count("doi") + (len(list(citations)) if citations else 0)
        )
        citation_density = float(c_hits) / max(1.0, len(text) / 1000.0)

        # methods presence with negation override
        has_methods = 1.0 if any(m in t for m in self.METHOD_MARKERS) else 0.0
        if any(n in t for n in self.NEGATION_MARKERS):
            has_methods = 0.0

        # naive gendered term count
        gendered = sum(t.count(g) for g in self.GENDERED)

        return [citation_density, has_methods, float(gendered)]
