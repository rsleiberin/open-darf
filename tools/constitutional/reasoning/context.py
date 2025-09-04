from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Tuple

@dataclass(frozen=True)
class ReasoningInput:
    decision: str                    # tri-state decision as string
    principles: List[str]            # applied principles identifiers
    rationale: str                   # short deterministic rationale string
    evidence_ids: List[str] = field(default_factory=list)  # links to evidence

@dataclass(frozen=True)
class ExplanationMeta:
    confidence: float                # 0.0 - 1.0
    uncertainty_note: str = ""       # short note if any

@dataclass(frozen=True)
class Explanation:
    decision: str
    applied_principles: Tuple[str, ...]
    reasoning_path: Tuple[str, ...]          # normalized steps
    cited_precedents: Tuple[str, ...]        # stable precedent IDs
    meta: ExplanationMeta
