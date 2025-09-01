#!/usr/bin/env python3
from __future__ import annotations

from typing import Dict, Iterable, Tuple, Set

# Allowed type combos → default relation label
_ALLOWED = {
    # orderless pairs of entity types → relation label
    frozenset(("Gene", "Disease")): "assoc",
    frozenset(("Protein", "Disease")): "assoc",
    frozenset(("Gene", "Gene")): "interacts",
}


def predict_heuristic(
    candidates: Iterable[Tuple[str, str]],
    ent_types: Dict[str, str],
) -> Set[Tuple[str, str, str]]:
    """Return typed relation predictions (head, tail, rtype) using static rules.
    (head, tail) must already be ordered lexicographically in `candidates`.
    """
    preds: Set[Tuple[str, str, str]] = set()
    for h, t in candidates:
        et = frozenset((ent_types.get(h, "UNK"), ent_types.get(t, "UNK")))
        r = _ALLOWED.get(et)
        if r:
            preds.add((h, t, r))
    return preds
