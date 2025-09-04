"""
Reasoning/explanation infrastructure for constitutional decisions (Phase 7D).
Deterministic fast-path explanations with precedent hooks and audit enrichment.
"""
from .context import ReasoningInput, Explanation, ExplanationMeta
from .engine import ExplanationEngine
from .precedent import PrecedentStore, LocalPrecedentStore, Neo4jPrecedentStore

__all__ = [
    "ReasoningInput",
    "Explanation",
    "ExplanationMeta",
    "ExplanationEngine",
    "PrecedentStore",
    "LocalPrecedentStore",
    "Neo4jPrecedentStore",
]
