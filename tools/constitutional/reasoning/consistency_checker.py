from __future__ import annotations
from typing import Dict, List, Tuple
from .precedent import PrecedentStore, LocalPrecedentStore, Neo4jPrecedentStore
from . import governance
import os

def _get_store() -> PrecedentStore:
    if os.getenv("NEO4J_URI") and os.getenv("NEO4J_USER") and os.getenv("NEO4J_PASSWORD"):
        return Neo4jPrecedentStore()
    return LocalPrecedentStore(os.getenv("REASONING_PRECEDENT_PATH", "var/state/precedents.jsonl"))

def check_consistency(decision: str, principles: List[str], topk: int = 3) -> Tuple[bool, Dict]:
    """
    Compare proposed decision vs. similar precedents' decisions (if stored).
    Returns (is_consistent, details).
    """
    store = _get_store()
    cfg = governance.load()
    ids = governance.filter_precedents(cfg, store.find_similar(principles, topk=topk))
    mismatches = []
    checked = []
    # Apply principle-based override to proposed decision, if configured
    decision_eff, gov_applied = governance.maybe_override_decision(cfg, decision, principles)
    for pid in ids:
        rec = store.get(pid) or {}
        prev_dec = rec.get("decision")
        if prev_dec is None:
            continue
        checked.append({"id": pid, "decision": prev_dec, "principles": rec.get("principles", [])})
        if prev_dec != decision_eff:
            mismatches.append({"id": pid, "prev_decision": prev_dec})
    return (len(mismatches) == 0, {"checked": checked, "mismatches": mismatches, "proposed": decision_eff, "principles": principles, "governance_applied": gov_applied})
