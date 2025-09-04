from __future__ import annotations
from typing import Dict
from .context import Explanation

def enrich_event(event: Dict, explanation: Explanation) -> Dict:
    """Return a copy of event with 'reasoning' payload attached (non-breaking)."""
    out = dict(event)
    out["reasoning"] = {
        "decision": explanation.decision,
        "applied_principles": list(explanation.applied_principles),
        "reasoning_path": list(explanation.reasoning_path),
        "cited_precedents": list(explanation.cited_precedents),
        "confidence": explanation.meta.confidence,
        "uncertainty_note": explanation.meta.uncertainty_note,
    }
    return out
