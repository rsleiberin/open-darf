from __future__ import annotations
from dataclasses import dataclass, field, asdict
from typing import Dict, List, Tuple, Optional
import sys
import uuid
import json

# Python 3.10+ supports dataclass(slots=True); older versions do not.
DATACLASS_KW = {"slots": True} if sys.version_info >= (3, 10) else {}


def new_id(prefix: str = "hg") -> str:
    """Compact unique id with stable prefix."""
    return f"{prefix}_{uuid.uuid4().hex}"


@dataclass(**DATACLASS_KW)
class Span:
    start: int
    end: int
    text: str


@dataclass(**DATACLASS_KW)
class Entity:
    uid: str
    etype: str
    name: str
    span: Optional[Span] = None
    props: Dict[str, str] = field(default_factory=dict)


@dataclass(**DATACLASS_KW)
class HyperEdge:
    """N-ary relation via a single hyperedge node with role-labeled participants."""

    uid: str
    relation: str
    # participants: list of (role_name, entity_uid)
    participants: List[Tuple[str, str]]
    props: Dict[str, str] = field(default_factory=dict)


@dataclass(**DATACLASS_KW)
class Fact:
    """A relation instance + provenance + scoring for ranking."""

    uid: str
    edge: HyperEdge
    doc_id: Optional[str] = None
    chunk_id: Optional[str] = None
    offsets: Optional[Tuple[int, int]] = None
    confidence: float = 0.0
    props: Dict[str, str] = field(default_factory=dict)

    def to_json(self) -> str:
        return json.dumps(asdict(self), ensure_ascii=False, separators=(",", ":"))
