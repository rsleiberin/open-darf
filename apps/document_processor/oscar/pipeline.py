# SPDX-License-Identifier: MIT
from __future__ import annotations
from typing import Dict, List, Tuple

from .engine import TinyObjectiveSubstitutionEngine, ObjectiveSubstitutionEngine
from .fidelity import TinySemanticFidelityValidator, SemanticFidelityValidator


def neutralize_preserving_semantics(
    biased_content: str,
    bias_type: str,
    *,
    engine: ObjectiveSubstitutionEngine = None,
    validator: SemanticFidelityValidator = None,
    min_fidelity: float = 0.95,
) -> Dict[str, object]:
    """
    Returns:
      {
        "candidate": <str or None>,
        "fidelity": <float>,
        "human_review": <bool>
      }
    Policy:
      - Prefer the best CHANGED candidate that meets min_fidelity.
      - If no changed candidate meets the threshold but the original does,
        return no change (candidate=None, human_review=True).
    """
    engine = engine or TinyObjectiveSubstitutionEngine()
    validator = validator or TinySemanticFidelityValidator()

    # Build candidate pool = engine suggestions (dedup) + original (at the end)
    pool: List[str] = []
    for c in engine.generate_alternatives(
        biased_content, bias_type=bias_type, num_candidates=5
    ):
        if c not in pool:
            pool.append(c)
    if biased_content not in pool:
        pool.append(biased_content)

    scored: List[Tuple[str, float]] = [
        (c, validator.compare_semantic_preservation(biased_content, c)) for c in pool
    ]
    # Separate changed vs original
    changed = [(c, s) for c, s in scored if c != biased_content]
    orig_score = next((s for c, s in scored if c == biased_content), 0.0)

    # Pick best changed candidate meeting threshold
    if changed:
        best_changed = max(changed, key=lambda cs: cs[1])
        if best_changed[1] >= min_fidelity:
            return {
                "candidate": best_changed[0],
                "fidelity": float(best_changed[1]),
                "human_review": False,
            }

    # Otherwise, if only original meets threshold -> no auto change, flag review
    if orig_score >= min_fidelity:
        return {"candidate": None, "fidelity": float(orig_score), "human_review": True}

    # Nothing meets threshold
    best_any = max(scored, key=lambda cs: cs[1]) if scored else (None, 0.0)
    return {"candidate": None, "fidelity": float(best_any[1]), "human_review": True}


def neutralize_text_for_flags(
    text: str,
    flags: Dict[str, float],
    *,
    engine: ObjectiveSubstitutionEngine = None,
    validator: SemanticFidelityValidator = None,
    min_fidelity: float = 0.95,
) -> Dict[str, object]:
    """
    Applies neutralization sequentially for each flagged bias (flag == 1.0).
    Returns:
      {
        "text": <possibly modified text>,
        "changes": [ { "bias_type": str, "fidelity": float }... ],
        "human_review": bool
      }
    """
    engine = engine or TinyObjectiveSubstitutionEngine()
    validator = validator or TinySemanticFidelityValidator()

    current = text
    changes: List[Dict[str, object]] = []
    human_review = False

    for bias_type, flag in flags.items():
        if not flag:
            continue
        res = neutralize_preserving_semantics(
            current,
            bias_type,
            engine=engine,
            validator=validator,
            min_fidelity=min_fidelity,
        )
        if res["candidate"] is not None:
            current = res["candidate"]
            changes.append({"bias_type": bias_type, "fidelity": float(res["fidelity"])})
        else:
            human_review = True

    return {"text": current, "changes": changes, "human_review": human_review}
