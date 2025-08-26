from __future__ import annotations
from typing import List, Dict

try:
    from typing import Protocol  # Python 3.8+: available; else fallback
except Exception:  # pragma: no cover

    class Protocol:  # type: ignore
        pass


from .model import Entity, HyperEdge


class GraphStore(Protocol):
    def upsert_entity(self, e: Entity) -> None: ...
    def upsert_hyperedge(self, h: HyperEdge) -> None: ...
    def relate(self, h: HyperEdge) -> None: ...


class VectorIndex(Protocol):
    def upsert(self, uid: str, vector: List[float], payload: Dict) -> None: ...
    def search(self, vector: List[float], top_k: int = 10) -> List[Dict]: ...


class NullVectorIndex:
    """No-op index to keep tests service-free."""

    def upsert(self, uid: str, vector: List[float], payload: Dict) -> None: ...
    def search(self, vector: List[float], top_k: int = 10) -> List[Dict]:
        return []
