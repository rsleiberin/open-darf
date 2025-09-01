"""Stdlib-only helpers for deterministic relation receipts."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List, Set, Tuple, Dict


@dataclass(frozen=True)
class Entity:
    eid: str
    etype: str
    sent: int


@dataclass(frozen=True)
class Relation:
    head: str
    tail: str
    rtype: str


def generate_candidates(entities: Iterable[Entity]) -> List[Tuple[str, str]]:
    """All unordered pairs of entities that occur in the same sentence.
    Returns pairs as sorted (head, tail) id tuples; no self-pairs.
    """
    by_sent: Dict[int, List[Entity]] = {}
    for e in entities:
        by_sent.setdefault(e.sent, []).append(e)
    pairs: Set[Tuple[str, str]] = set()
    for bucket in by_sent.values():
        n = len(bucket)
        for i in range(n):
            for j in range(i + 1, n):
                a, b = bucket[i].eid, bucket[j].eid
                head, tail = (a, b) if a < b else (b, a)
                pairs.add((head, tail))
    return sorted(pairs)


def micro_prf1(
    gold: Set[Tuple[str, str, str]], pred: Set[Tuple[str, str, str]]
) -> Tuple[float, float, float, int]:
    """Micro P/R/F1 over typed relations (head, tail, rtype)."""
    tp = len(gold & pred)
    fp = len(pred - gold)
    fn = len(gold - pred)
    precision = tp / (tp + fp) if (tp + fp) else 0.0
    recall = tp / (tp + fn) if (tp + fn) else 0.0
    f1 = (
        (2 * precision * recall / (precision + recall)) if (precision + recall) else 0.0
    )
    support = len(gold)
    return precision, recall, f1, support
