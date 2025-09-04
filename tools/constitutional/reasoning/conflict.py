from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, List, Tuple
import json, os

Decision = str  # 'ACCEPTABLE' | 'REJECTED' | 'PENDING'
Vote = str      # 'ALLOW' | 'DENY' | 'ABSTAIN' | 'PENDING'

@dataclass(frozen=True)
class PrincipleVote:
    principle: str
    vote: Vote  # normalized to upper-case tokens above

def _norm(s: str) -> str:
    return " ".join(s.strip().split()).lower()

def _weights() -> Dict[str, float]:
    """Load weights from REASONING_WEIGHTS_JSON (e.g., {"safety":2.0}). Defaults to 1.0."""
    raw = os.getenv("REASONING_WEIGHTS_JSON", "").strip()
    if not raw:
        return {}
    try:
        data = json.loads(raw)
        return { _norm(k): float(v) for k, v in data.items() }
    except Exception:
        return {}

def _w_for(p: str, W: Dict[str, float]) -> float:
    return float(W.get(_norm(p), 1.0))

def resolve(votes: List[PrincipleVote]) -> Tuple[Decision, Dict]:
    """
    Deterministic conflict resolution:
      1) Strict DENY precedence: any DENY ⇒ REJECTED (fail-closed governance).
      2) Otherwise, compute weighted ALLOW mass; if >0 ⇒ ACCEPTABLE; if none ⇒ PENDING.
    Returns: (decision, rationale_dict) for audit/explanations.
    Formal properties:
      - Commutative: order-independent
      - Idempotent: duplicate votes do not change decision semantics
    """
    # Normalize & collapse duplicates by max severity: DENY > ALLOW > (ABSTAIN|PENDING)
    collapsed: Dict[str, Vote] = {}
    severity = {"DENY": 3, "ALLOW": 2, "ABSTAIN": 1, "PENDING": 1}
    for pv in votes:
        p = _norm(pv.principle)
        v = pv.vote.strip().upper()
        v = v if v in ("ALLOW","DENY","ABSTAIN","PENDING") else "ABSTAIN"
        if p in collapsed:
            if severity[v] > severity[collapsed[p]]:
                collapsed[p] = v
        else:
            collapsed[p] = v

    # 1) Strict DENY precedence
    deny_set = [pr for pr, v in collapsed.items() if v == "DENY"]
    if deny_set:
        return ("REJECTED", {
            "rule": "deny_precedence",
            "deny_principles": deny_set,
            "weights_considered": False
        })

    # 2) Weighted ALLOW mass (informational; weights never override DENY)
    W = _weights()
    allow_mass = sum(_w_for(pr, W) for pr, v in collapsed.items() if v == "ALLOW")
    decision: Decision = "ACCEPTABLE" if allow_mass > 0 else "PENDING"
    return (decision, {
        "rule": "allow_weight_mass" if allow_mass > 0 else "no_allow_then_pending",
        "allow_mass": allow_mass,
        "weights_considered": True,
        "principles": [{"principle": pr, "vote": v, "weight": _w_for(pr, W)} for pr, v in sorted(collapsed.items())],
    })
