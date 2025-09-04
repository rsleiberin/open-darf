from __future__ import annotations
import os
from typing import Dict, Iterable, List
from .engine import ExplanationEngine
from .context import ReasoningInput
from .audit_ext import enrich_event
from .conflict import PrincipleVote, resolve
from . import resolution_patterns
from .precedent import LocalPrecedentStore, Neo4jPrecedentStore, PrecedentStore
from . import governance

def _enabled() -> bool:
    v = os.getenv("REASONING_ENABLE", "0")
    return v not in ("0", "", "false", "False")

def _write_enabled() -> bool:
    v = os.getenv("REASONING_PRECEDENT_WRITE", "0")
    return v not in ("0", "", "false", "False")

def _local_path() -> str:
    return os.getenv("REASONING_PRECEDENT_PATH", "var/state/precedents.jsonl")

# Lazy singletons
_ENGINE = ExplanationEngine()
_STORE: PrecedentStore | None = None

def _get_store() -> PrecedentStore:
    global _STORE
    if _STORE is not None:
        return _STORE
    # Prefer Neo4j if creds are present, else Local
    if os.getenv("NEO4J_URI") and os.getenv("NEO4J_USER") and os.getenv("NEO4J_PASSWORD"):
        _STORE = Neo4jPrecedentStore()
    else:
        _STORE = LocalPrecedentStore(_local_path())
    return _STORE

def cite_precedents(principles: List[str], topk: int = 3) -> List[str]:
    """Return similar precedent IDs for given principle set, filtered by governance."""
    store = _get_store()
    ids = store.find_similar(principles, topk=topk)
    cfg = governance.load()
    return governance.filter_precedents(cfg, ids)

def record_precedent(precedent_id: str, principles: List[str], rationale: str) -> None:
    """Write/update a precedent when write flag is enabled; skip deprecated IDs."""
    if not _write_enabled():
        return
    cfg = governance.load()
    if governance.is_deprecated(cfg, precedent_id):
        return
    store = _get_store()
    store.upsert(precedent_id, principles, rationale)

def maybe_enrich_event(event: Dict, decision: str, principles: List[str], rationale: str, evidence_ids: List[str], votes: List[PrincipleVote] | None = None) -> Dict:
    """
    If REASONING_ENABLE is set, attach a compact, deterministic explanation to the event,
    including cited precedents (if any). Otherwise, return the original event.
    """
    if not _enabled():
        return dict(event)
    rin = ReasoningInput(
        decision=decision,
        principles=principles,
        rationale=rationale,
        evidence_ids=evidence_ids,
    )
    cited = tuple(cite_precedents(principles, topk=3))
    exp = _ENGINE.explain(rin, precedents=cited)
    enriched = enrich_event(event, exp)
    # include resolver rationale when votes are provided (non-breaking)
    if votes:
        _, rationale_obj = resolve(votes)
        enriched.setdefault('reasoning', {})['conflict_rationale'] = rationale_obj
        if _pattern_write_enabled():
            try:
                resolution_patterns.write_pattern(votes, decision, rationale_obj)
            except Exception:
                pass
    return enriched


def _pattern_write_enabled() -> bool:
    v = os.getenv("REASONING_PATTERN_WRITE", "0")
    return v not in ("0", "", "false", "False")

def record_conflict_pattern(votes: list[PrincipleVote], decision: str) -> str | None:
    if not _pattern_write_enabled():
        return None
    dec, rationale = resolve(votes)
    # prefer the resolver's decision (governed) for storage to ensure consistency
    return resolution_patterns.write_pattern(votes, dec, rationale)
