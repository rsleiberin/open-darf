from __future__ import annotations
from typing import Dict
from .context import Explanation

def quality_score(exp: Explanation) -> Dict[str, float]:
    """
    Deterministic heuristic:
      base = 0.5
      +0.1 per applied principle (max +0.4)
      +0.1 if reasoning_path non-empty
      cap at 1.0
    """
    base = 0.5
    bonus = min(0.4, 0.1 * len(exp.applied_principles))
    path = 0.1 if len(exp.reasoning_path) > 0 else 0.0
    score = min(1.0, base + bonus + path)
    return {"score": score, "principles": float(len(exp.applied_principles)), "path_bonus": path}
