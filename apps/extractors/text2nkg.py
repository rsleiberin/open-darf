from __future__ import annotations

import os
import re
from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional

ENABLE_ENV = "EXTRACTOR_NKG"


@dataclass(frozen=True)
class Hyperedge:
    head: str  # subject
    relation: str  # predicate
    tail: str  # object
    qualifiers: Dict[str, str] = field(default_factory=dict)


_REL_MAP = {
    r"\b(inhibits|represses)\b": "INHIBITS",
    r"\b(activates|induces)\b": "ACTIVATES",
    r"\b(binds|interacts with)\b": "BINDS",
}

_TOKEN_RE = r"[A-Za-z0-9\-_/\.]+"


def is_enabled(env: Optional[dict] = None) -> bool:
    e = env if env is not None else os.environ
    return str(e.get(ENABLE_ENV, "")).strip().lower() in {"1", "true", "yes", "on"}


def _iter_edges(text: str) -> Iterable[Hyperedge]:
    for pat, rel in _REL_MAP.items():
        # Simple SVO pattern: HEAD <rel> TAIL
        regex = re.compile(rf"\b({_TOKEN_RE})\s+{pat}\s+({_TOKEN_RE})\b", re.IGNORECASE)
        for m in regex.finditer(text):
            head, tail = m.group(1), m.group(
                len(m.groups())
            )  # first and last capture groups
            yield Hyperedge(head=head, relation=rel, tail=tail)


def validate(edge: Hyperedge) -> bool:
    if not edge.head or not edge.tail or not edge.relation:
        return False
    if edge.relation not in {"INHIBITS", "ACTIVATES", "BINDS"}:
        return False
    # basic token sanity
    tok = re.compile(rf"^{_TOKEN_RE}$")
    return bool(tok.match(edge.head) and tok.match(edge.tail))


def extract(text: str) -> List[Hyperedge]:
    if not is_enabled():
        raise RuntimeError("Text2NKG extractor disabled — set EXTRACTOR_NKG=1")
    if not text:
        return []
    edges = [e for e in _iter_edges(text) if validate(e)]
    # append-only receipt (best-effort)
    try:
        from apps.audit import receipts  # type: ignore

        receipts.make_jsonl_sink("text2nkg")(
            {"component": "text2nkg_stub", "event": "extract", "count": len(edges)}
        )
    except Exception:
        pass
    return edges
